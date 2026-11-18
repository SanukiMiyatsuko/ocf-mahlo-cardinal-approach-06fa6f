import Mahlo.FS.PsiLim

/-! `Ξ_m(q)` への崩壊 `t = Ψ_{Ξ_m(q)}(X'+1)` の列のうち、`q < M_m` で `q < X'` のもの。

このとき `p = Ψ_{Ξ_m(q)}(X')` は標準形で（`psi_pred_wnf`）、`q < p`（`lt_seed`）。`Ξ_m(q)` 未満の `Ξ_m(f)` は
全て `p` 未満（`xi_lt_seed`）なので、`t` 未満の項は `p` の上の `Ω` の塔で押さえられ（`cof_tower`）、列は
`t[n] = Ω_{Ω_{⋯Ω_{p+1}⋯+1}+1}`（`n+1` 段）になる（`inv_psi_succ_xi_small`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 補題 -/

theorem xi_lt_M {m : Nat} (a : Tm) : Lt (.Xi m a) (.M m) :=
  lt_of_lev_lt' (by simp only [lev]; omega)

/-- `a < M_m` なら `a < Ξ_m(a)` -/
theorem lt_xi_self {m : Nat} {a : Tm} (h : WNF (.Xi m a)) (ha : Lt a (.M m)) : Lt a (.Xi m a) :=
  coll_xi0 h a h.xi.2.1 (xi_selfY h) ha

theorem WNF.mk_xi {m : Nat} {a : Tm} (hm : 1 ≤ m) (ha : WNF a) (hle : cmp a (succM m) ≠ .gt)
    (hC : inC a a (.M m) = true) : WNF (.Xi m a) := by
  show isNF (.Xi m a) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨⟨hm, ha⟩, hle⟩, hC⟩

/-- `Ξ_m(q)`（`q < M_m`）の下の `Ξ_m(a)`（`a < q`）は標準形で `Ξ_m(q)` 未満 -/
theorem xi_below {m : Nat} {q a : Tm} (hπ : WNF (.Xi m q)) (hq : Lt q (.M m)) (ha : WNF a)
    (haq : Lt a q) : WNF (.Xi m a) ∧ Lt (.Xi m a) (.Xi m q) := by
  obtain ⟨hm, hqF, hle, -⟩ := hπ.xi
  have hMF := WNF.M' hm
  have haM : Lt a (.M m) := lt_transY ha hqF hMF haq hq
  have hxF : WNF (.Xi m a) := WNF.mk_xi hm ha
    (ne_gt_of_le (Or.inr (lt_of_lt_of_leY ha hqF (WNF.succM hm) haq (le_of_ne_gtY hqF (WNF.succM hm) hle))))
    (inC_of_lt_cut (Cut.of_wnf hMF) a ha haM)
  refine ⟨hxF, (lt_xi_xi0 (fun e => Lt.ne haq e)).mpr (Or.inl ⟨haq, ?_⟩)⟩
  exact inC_of_lt_cut (Cut.of_wnf hπ) q ha (lt_transY ha hqF hπ haq (lt_xi_self hπ hq))

/-- `Ψ_π(X'+1)` が標準形で、`Ξ` への崩壊なら `d < X'` のとき、`Ψ_π(X')` も標準形 -/
theorem psi_pred_wnf {π X : Tm} (h : WNF (.Psi π X)) (hs : isSucc X = true)
    (hv : ∀ n d, π = .Xi n d → Lt d (predT X)) : WNF (.Psi π (predT X)) := by
  have hP := h.psi
  have hXF := hP.aF
  have hπF := hP.piF
  have hT := hP.tgt
  have hpF := predT_WNF hXF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  refine WNF.mk_psi ⟨hT, hπF, hpF, hv, ?_⟩
  have hbC : inC (predT X) X (.Psi π X) = true := by
    refine (inC_iff_summands _ _ _).mpr (fun s hs' => ?_)
    rw [summands_predT hXF hys] at hs'
    exact (inC_iff_summands _ _ _).mp hP.Ca s (by rw [hys]; exact List.mem_append_left _ hs')
  refine inC_mono_node _ _ _ _ _ hbC (fun v hv' _ hvt => ?_)
    (fun v hv' hvs hvc => lt_pred_of_lt_succ hXF hs (hpF.of_mem_subs hv') hvc (ne_of_mem_subs_lt hvs))
  have hvF := hpF.of_mem_subs hv'
  refine below_transfer hπF hT v hvF (fun Y hYs hYX => ?_) hvt
  have hYF := (hvF.of_mem_subs hYs).psi.aF
  refine lt_pred_of_lt_succ hXF hs hYF hYX (fun e => ?_)
  have h1 := size_le_of_mem_subs hYs
  have h2 := size_le_of_mem_subs hv'
  rw [e] at h1
  simp only [Tm.size] at h1
  omega

/-- `Ψ_π(X')` が `X'+1` の部分項なら `Ψ_π(X') = 1` -/
theorem psi_pred_mem_one {π X : Tm} (hX : WNF X) (hs : isSucc X = true)
    (hw : Tm.Psi π (predT X) ∈ subs X) : Tm.Psi π (predT X) = one := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hszp : ∀ s, s ∈ ys → Tm.Psi π (predT X) ∈ subs s → False := by
    intro s hs1 hws
    have hsp : s ∈ subs (predT X) :=
      mem_subs_of_mem_summands (by rw [summands_predT hX hys]; exact hs1)
    have h1 := size_le_of_mem_subs hws
    have h2 := size_le_of_mem_subs hsp
    simp only [Tm.size] at h1
    omega
  rcases subs_sum_cases hw with ⟨L, hL⟩ | ⟨s, hs', hws⟩
  · rw [hys] at hL
    have hL' : ys ++ [one] = L ++ [Tm.Psi π (predT X)] := hL
    have := congrArg List.getLast? hL'
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at this
    exact (Option.some.inj this).symm
  · rw [hys] at hs'
    rcases List.mem_append.mp hs' with hs1 | hs1
    · exact absurd hws (fun hh => hszp s hs1 hh)
    · rw [List.mem_singleton.mp hs1] at hws
      rcases mem_subs_one hws with e | e | e
      · exact e
      · cases e
      · cases e

/-- `Ψ_π(X'+1)` の真の部分項で `Ψ_π(X'+1)` 未満のものは `Ψ_π(X')` 未満（`π ≠ Ω_0`） -/
theorem gap_psi_pred {π X : Tm} (h : WNF (.Psi π X)) (hs : isSucc X = true)
    (hπ0 : π ≠ .Om .zero) :
    ∀ v, v ∈ subs (Tm.Psi π X) → v ≠ .Psi π X → Lt v (.Psi π X) → Lt v (.Psi π (predT X)) := by
  have hP := h.psi
  have hXF := hP.aF
  have hπF := hP.piF
  have hT := hP.tgt
  intro v hv hne hvt
  have hvF := h.of_mem_subs hv
  simp only [subs, List.mem_cons, List.mem_append] at hv
  rcases hv with e | hvπ | hvX
  · exact absurd e hne
  · have hlt : Lt v π := lt_transY hvF h hπF hvt (lt_psi_targetY h)
    exact sub_lt_psi hπF hT (predT X) v hvπ (Lt.ne hlt) hvF hlt
  · refine below_transfer hπF hT v hvF (fun Y hYs hYX => ?_) hvt
    have hYF := (hvF.of_mem_subs hYs).psi.aF
    refine lt_pred_of_lt_succ hXF hs hYF hYX (fun e => ?_)
    rw [e] at hYs
    have h1 : Tm.Psi π (predT X) = Tm.Psi (.Om .zero) .zero :=
      psi_pred_mem_one hXF hs (subs_trans hvX hYs)
    exact hπ0 (Tm.Psi.inj h1).1

/-! ### 種 `p = Ψ_{Ξ_m(q)}(γ)` -/

/-- `q < Ψ_{Ξ_m(q)}(γ)`（`q < M_m`） -/
theorem lt_seed {m : Nat} {q γ : Tm} (hp : WNF (.Psi (.Xi m q) γ)) (hq : Lt q (.M m)) :
    Lt q (.Psi (.Xi m q) γ) := by
  have hP := hp.psi
  have hπF := hP.piF
  have hqF := hπF.xi.2.1
  have hγ := hP.aF
  obtain ⟨-, hC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hp)
  have hC' : inC q γ (.Psi (.Xi m q) γ) = true :=
    inC_mono_node q q _ γ _ hC (fun _ _ _ h => h)
      (fun v hv _ hvq => lt_transY (hqF.of_mem_subs hv) hqF hγ hvq (hP.act m q rfl))
  exact coll_psiY hp hqF hC' (lt_xi_self hπF hq)

/-- `q < Ψ_{Ξ_m(q)}(γ)` なら、`Ξ_m(q)` 未満の `Ξ_m(f)` は `Ψ_{Ξ_m(q)}(γ)` 未満 -/
theorem xi_lt_seed {m : Nat} {q γ f : Tm} (hp : WNF (.Psi (.Xi m q) γ))
    (hqp : Lt q (.Psi (.Xi m q) γ)) (hf : WNF (.Xi m f)) (hfπ : Lt (.Xi m f) (.Xi m q)) :
    Lt (.Xi m f) (.Psi (.Xi m q) γ) := by
  have hP := hp.psi
  have hπF := hP.piF
  have hqF := hπF.xi.2.1
  have hfF := hf.xi.2.1
  obtain ⟨hk, hC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hp)
  have hgt : cmp (.Xi m q) (.Xi m f) = .gt := by
    rw [swapY hf hπF]
    have : cmp (.Xi m f) (.Xi m q) = .lt := hfπ
    rw [this]; rfl
  rcases triY hf hp with h | h | h
  · exact h
  · cases h
  · exfalso
    have hne : f ≠ q := fun e => Lt.ne hfπ (by rw [e])
    rcases (lt_xi_xi0 hne).mp hfπ with ⟨hfq, -⟩ | ⟨hqf, hnC⟩
    · -- `f < q < p`
      have hfp : Lt f (.Psi (.Xi m q) γ) := lt_transY hfF hqF hp hfq hqp
      have hb : baseOf (.Xi m f) (.Psi (.Xi m q) γ) = true :=
        (baseOf_xi_iff m f _).mpr ⟨hk, inC_of_lt_cut (Cut.of_wnf hp) f hfF hfp⟩
      exact Lt.asymmY hp hf h ((lt_xi_psi_iff rfl).mpr ⟨hgt, hb⟩)
    · -- `q < f`：`q ∈ C(q, p)` から `q ∈ C(f, Ξ_m(f))`
      have : inC q f (.Xi m f) = true :=
        inC_mono_node q q _ f _ hC
          (fun v hv _ hvp => lt_transY (hqF.of_mem_subs hv) hp hf hvp h)
          (fun v hv _ hvq => lt_transY (hqF.of_mem_subs hv) hqF hfF hvq hqf)
      rw [this] at hnC
      cases hnC

/-! ### `Ω` の塔 -/

theorem wnf_tower {G : Tm} (hG : WNF G) : ∀ k, WNF (tower G k)
  | 0 => hG
  | k + 1 => WNF.om_succT (wnf_tower hG k)

theorem tower_lt_succ {G : Tm} (hG : WNF G) (k : Nat) : Lt (tower G k) (tower G (k + 1)) :=
  lt_succT_om (wnf_tower hG k)

theorem tower_le_mono {G : Tm} (hG : WNF G) {i k : Nat} (h : i ≤ k) :
    Le (tower G i) (tower G k) := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ ih =>
    exact Or.inr (lt_of_le_of_ltY (wnf_tower hG _) (wnf_tower hG _) (wnf_tower hG _) ih
      (tower_lt_succ hG _))

/-- `Ω` の不動点 `t` について、`G < t` なら塔も `t` 未満 -/
theorem tower_lt_OF {G t : Tm} (hG : WNF G) (ht : WNF t) (hOF : IsOF t) (hGt : Lt G t) :
    ∀ k, Lt (tower G k) t
  | 0 => hGt
  | k + 1 => by
    have ih := tower_lt_OF hG ht hOF hGt k
    have hTF := wnf_tower hG k
    show Lt (.Om (succT (tower G k))) t
    refine (lt_om_OFG hOF ht).mpr (succT_lt_of_not_succ hTF ht (fun hs => ?_) ih)
    rw [isSucc_principal hOF.principal] at hs
    exact hOF.ne_one (beq_iff_eq.mp hs)

/-- 塔は `C(g, d)` に入る -/
theorem inC_tower {G g d : Tm} (hg0 : g ≠ .zero) (hG : inC G g d = true) :
    ∀ k, inC (tower G k) g d = true
  | 0 => hG
  | k + 1 => by
    show inC (.Om (succT (tower G k))) g d = true
    rw [inC_om]
    exact inC_succT (inC_one hg0) (inC_tower hg0 hG k)

/-! ### 塔の共終性 -/

/-- `t = Ψ_{Ξ_m(q)}(X)` 未満の `Ξ_m(f)` と、崩壊先が `Ξ_m(q)` 以上の階 `m` の崩壊が全て `s` 以下なら、
    `t` 未満の標準形は `s` の上の `Ω` の塔で押さえられる -/
theorem cof_tower {m : Nat} {q X s : Tm} (ht : WNF (.Psi (.Xi m q) X)) (hs : WNF s)
    (hs1 : lev (tower s 1) = m)
    (Hxi : ∀ f, WNF (.Xi m f) → Lt (.Xi m f) (.Psi (.Xi m q) X) → Le (.Xi m f) s)
    (Hpsi : ∀ ρ b, WNF (.Psi ρ b) → Lt (.Psi ρ b) (.Psi (.Xi m q) X) → lev ρ = m →
      ¬ Lt ρ (.Xi m q) → Le (.Psi ρ b) s) :
    ∀ x, WNF x → Lt x (.Psi (.Xi m q) X) → ∃ k, Lt x (tower s k) := by
  have hπF := ht.psi.piF
  have hm := hπF.xi.1
  have hOF : IsOF (Tm.Psi (.Xi m q) X) := Or.inr ⟨m, q, X, rfl⟩
  have hT1F : WNF (tower s 1) := wnf_tower hs 1
  have hT1 : lev (tower s 1) = m := hs1
  have hle1 : ∀ y, WNF y → Le y s → Lt y (tower s 1) := fun y hy h =>
    lt_of_le_of_ltY hy hs hT1F h (tower_lt_succ hs 0)
  intro x
  induction x using size_induction with
  | h x ih =>
  intro hx hxt
  have hlev : lev x ≤ m := by
    have := lev_le_of_lt_gen hxt; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact ⟨1, lt_of_lev_lt' (by rw [hT1]; exact hl)⟩
  cases x with
  | zero =>
    simp only [lev] at hl
    rw [← hl] at hm
    exact absurd hm (by decide)
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hx.plus
    obtain ⟨k, hk⟩ := ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hx ht (lt_plus_leftY hx) hxt)
    have hk' : Lt a (tower s (k + 1)) :=
      lt_transY ha (wnf_tower hs k) (wnf_tower hs (k + 1)) hk (tower_lt_succ hs k)
    exact ⟨k + 1, (lt_plus_prin_iffY hx rfl).mpr hk'⟩
  | M k =>
    have hk : lev (Tm.M k) ≤ lev (tower s 1) := by rw [hT1]; exact Nat.le_of_eq hl
    exact ⟨1, bot_ltY rfl hk rfl rfl hT1F⟩
  | Om e =>
    have heF := hx.om.1
    have het : Lt e (.Psi (.Xi m q) X) := (lt_om_OFG hOF ht).mp hxt
    obtain ⟨k, hk⟩ := ih e (by simp only [Tm.size]; omega) heF het
    refine ⟨k + 1, ?_⟩
    show Lt (.Om e) (.Om (succT (tower s k)))
    exact lt_om_iffG.mpr
      (lt_transY heF (wnf_tower hs k) (succT_WNF (wnf_tower hs k)) hk (lt_succT _))
  | Xi k f =>
    simp only [lev] at hl
    subst hl
    exact ⟨1, hle1 _ hx (Hxi f hx hxt)⟩
  | Psi ρ b =>
    have hP := hx.psi
    have hρF := hP.piF
    have hlρ : lev ρ = m := by simpa [lev] using hl
    by_cases hρπ : Lt ρ (.Xi m q)
    · have hne : ρ ≠ .Xi m q := fun e => Lt.ne hρπ e
      have hnlt : ¬ Lt (.Xi m q) ρ := Lt.asymmY hρF hπF hρπ
      have hbase := (lt_psi_psi_ltT (β := b) (γ := X) (by rw [hlρ]; rfl) hne hnlt).mp hxt
      rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨k, e', rfl⟩
      · -- `ρ = Ω_0`
        refine ⟨1, lt_transY hx WNF.om_zero hT1F (lt_psi_targetY hx) ?_⟩
        show Lt (.Om .zero) (.Om (succT s))
        exact lt_om_iffG.mpr (zero_lt (succT_ne_zero s))
      · -- `ρ = Ω_c`（`c` は後者）：`Ω_{c-1} < t` から
        have hcF := hρF.om.1
        have hpF := predT_WNF hcF hc
        have hz := wnf_omOf hpF
        have hzt : Lt (omOf (predT c)) (.Psi (.Xi m q) X) := (baseOf_om_succ hc).mp hbase
        have hzs : (omOf (predT c)).size < (Tm.Psi (.Om c) b).size := by
          have := size_omOf_predT_lt hc
          simp only [Tm.size] at this ⊢
          omega
        obtain ⟨k, hk⟩ := ih _ hzs hz hzt
        have hTF := wnf_tower hs k
        have h1 : Lt (predT c) (tower s k) := lt_of_le_of_ltY hpF hz hTF (le_omOf hpF) hk
        have h2 : Le c (tower s k) := by
          have := succT_leY hpF hTF h1
          rwa [succT_predT hcF hc] at this
        have h3 : Lt c (succT (tower s k)) :=
          lt_of_le_of_ltY hcF hTF (succT_WNF hTF) h2 (lt_succT _)
        refine ⟨k + 1, lt_transY hx hρF (wnf_tower hs (k + 1)) (lt_psi_targetY hx) ?_⟩
        show Lt (.Om c) (.Om (succT (tower s k)))
        exact lt_om_iffG.mpr h3
      · -- `ρ = Ξ_m(e')`：`ρ < t`
        have hkm : k = m := by simpa [lev] using hlρ
        subst hkm
        have hgt : cmp (.Xi k q) (.Xi k e') = .gt := by
          rw [swapY hρF hπF]
          have : cmp (.Xi k e') (.Xi k q) = .lt := hρπ
          rw [this]; rfl
        have hρt : Lt (.Xi k e') (.Psi (.Xi k q) X) := (lt_xi_psi_iff rfl).mpr ⟨hgt, hbase⟩
        exact ⟨1, hle1 _ hx
          (Or.inr (lt_of_lt_of_leY hx hρF hs (lt_psi_targetY hx) (Hxi e' hρF hρt)))⟩
    · exact ⟨1, hle1 _ hx (Hpsi ρ b hx hxt hlρ hρπ)⟩

/-- `t[n]` が `s` から `n+1` 段の `Ω` の塔である列の不変量 -/
theorem natInv_tower {m : Nat} {q X s : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hf : ∀ n, fundNat (.Psi (.Xi m q) X) n = tower s (n + 1))
    (hs : WNF s) (hst : Lt s (.Psi (.Xi m q) X)) (hs1 : lev (tower s 1) = m)
    (Hxi : ∀ f, WNF (.Xi m f) → Lt (.Xi m f) (.Psi (.Xi m q) X) → Le (.Xi m f) s)
    (Hpsi : ∀ ρ b, WNF (.Psi ρ b) → Lt (.Psi ρ b) (.Psi (.Xi m q) X) → lev ρ = m →
      ¬ Lt ρ (.Xi m q) → Le (.Psi ρ b) s)
    (hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi (.Xi m q) X) g d = true →
      ¬ Lt (.Psi (.Xi m q) X) d → inC s g d = true)
    (hgap : ∀ v, v ∈ subs (Tm.Psi (.Xi m q) X) → v ≠ .Psi (.Xi m q) X →
      Lt v (.Psi (.Xi m q) X) → Le v s) :
    NatInv (.Psi (.Xi m q) X) := by
  have hOF : IsOF (Tm.Psi (.Xi m q) X) := Or.inr ⟨m, q, X, rfl⟩
  have hlt := tower_lt_OF hs ht hOF hst
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC => ?_, fun n v hv hne hvt => ?_, fun g d n _ _ _ hC => ?_⟩
  rotate_right
  · rw [hf] at hC ⊢
    have h1 : inC (.Om (succT (tower s (n + 1)))) g d = true := hC
    rw [inC_om] at h1
    exact inC_of_succT h1
  · rw [hf]; exact wnf_tower hs _
  · rw [hf]; exact hlt _
  · rw [hf, hf]; exact tower_lt_succ hs _
  · obtain ⟨k, hk⟩ := cof_tower ht hs hs1 Hxi Hpsi x hx hxt
    refine ⟨k, ?_⟩
    rw [hf]
    exact Or.inr (lt_transY hx (wnf_tower hs k) (wnf_tower hs (k + 1)) hk (tower_lt_succ hs k))
  · rw [hf]
    show Tm.Om _ ≠ .zero
    intro e; cases e
  · rw [hf]
    by_cases hd' : Lt (.Psi (.Xi m q) X) d
    · exact inC_of_lt_cut hd g (wnf_tower hs _) (hd _ _ (wnf_tower hs _) ht (hlt _) hd')
    · exact inC_tower hg0 (hub g d hg hg0 hd hC hd') _
  · rw [hf]
    exact lt_of_le_of_ltY (ht.of_mem_subs hv) hs (wnf_tower hs _) (hgap v hv hne hvt)
      (lt_of_lt_of_leY hs (wnf_tower hs 1) (wnf_tower hs (n + 1)) (tower_lt_succ hs 0)
        (tower_le_mono hs (by omega)))


/-! ### 列の記述：`q < M_m` なら塔 -/

theorem takeWhile_eq_nil {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x, x ∈ l → p x = false) → l.takeWhile p = []
  | [], _ => rfl
  | a :: _, h => by simp [List.takeWhile, h a List.mem_cons_self]

theorem first_app_xi_nat {τ : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hr : r.dom = .omega) (hx : WNF (r.nat 0)) :
    (SeqD.app τ (.xi m) pre R r .zero .zero).first = .Xi m (oadd (ofSummands pre) (r.nat 0)) := by
  have hd : (SeqD.app τ (.xi m) pre R r .zero .zero).dom = .omega := by
    simp only [SeqD.dom, hr]
  unfold SeqD.first
  rw [hd]
  simp only [SeqD.nat, hr, Gen.ap, combine]
  rw [zero_nsum _ hx, zero_nsum _ hx]

theorem first_app_xi_big {τ σ : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hr : r.dom = .big σ) (hστ : ltB σ τ = true) (hx : WNF (r.big .zero)) :
    (SeqD.app τ (.xi m) pre R r .zero .zero).first = .Xi m (oadd (ofSummands pre) (r.big .zero)) := by
  have hd : (SeqD.app τ (.xi m) pre R r .zero .zero).dom = .big σ := by
    simp only [SeqD.dom, hr, hστ, ↓reduceIte]
  unfold SeqD.first
  rw [hd]
  simp only [SeqD.big, Gen.ap, combine]
  rw [zero_nsum _ hx, zero_nsum _ hx]

/-- `q < M_m` なら、`Ξ_m(q)` の族の種 `p`（`q < p`、`Ξ_m(q)` 未満の `Ξ_m(f)` は `p` 未満）の上の閉包は
    `p` の上の `Ω` の塔 -/
theorem mahloVK_small {m : Nat} {q p : Tm} (hπ : WNF (.Xi m q)) (hq : Lt q (.M m)) (hp : WNF p)
    (hpl : Lt (kTerm (m - 1)) p) (hqp : Lt q p) (hpX : ∀ a, Tm.Xi m a ≠ p)
    (Hxi : ∀ f, WNF (.Xi m f) → Lt (.Xi m f) (.Xi m q) → Lt (.Xi m f) p)
    (hRinv : ∀ R, R ∈ summands q → Inv R) :
    mahloVK m q (info q).sums (.Xi m q) (some p) = .tower p := by
  obtain ⟨hm, hqF, -, -⟩ := hπ.xi
  have hqπ : Lt q (.Xi m q) := lt_xi_self hπ hq
  have hsumF : ∀ s, s ∈ summands q → WNF s := fun s hs => (summands_WNF q hqF s hs).1
  have hsum_le : ∀ s, s ∈ summands q → Le s q := fun s hs => le_of_mem_summands hqF hs
  have hmem : ∀ x, x ∈ (info q).sums → x.1 ∈ summands q := fun x hx => by
    rw [← info_sums_fst q]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
  -- `Ξ_m(a)`（`a < q`）は `p` 未満
  have hxa : ∀ a, WNF a → Lt a q → ltB p (.Xi m a) = false := by
    intro a ha haq
    obtain ⟨hxF, hxπ⟩ := xi_below hπ hq ha haq
    have h := Hxi a hxF hxπ
    cases e : ltB p (.Xi m a) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hxF hp h)
  unfold mahloVK
  by_cases hq0 : q = .zero
  · rw [ite_eq_left hq0]
    have h0 : ltB p (floorLev m) = false := by
      cases e : ltB p (floorLev m) with
      | false => rfl
      | true => exact absurd (ltB_iff.mp e) (Lt.asymmY (wnf_kTerm _) hp hpl)
    simp only [maxO, h0, Bool.false_eq_true, ↓reduceIte]
  · rw [ite_eq_right hq0]
    by_cases hqs : isSucc q = true
    · rw [ite_eq_left hqs]
      have hsp : splitPosD (.Xi m q) (info q).sums.dropLast = none := by
        have hTW : (info q).sums.dropLast.takeWhile (fun s => leB (.Xi m q) s.1) = [] := by
          refine takeWhile_eq_nil (fun x hx => ?_)
          have hx' := hmem x ((List.dropLast_sublist _).subset hx)
          have hxF := hsumF _ hx'
          cases e : leB (.Xi m q) x.1 with
          | false => rfl
          | true =>
            exfalso
            exact not_lt_of_leY hπ hxF (le_of_ne_gtY hπ hxF (leB_iff.mp e))
              (lt_of_le_of_ltY hxF hqF hπ (hsum_le _ hx') hqπ)
        unfold splitPosD
        rw [hTW]
        rfl
      have h' : ltB p (.Xi m (pred q)) = false :=
        hxa (pred q) (predT_WNF hqF hqs) (lt_predT hqF hqs)
      simp only [hsp, maxO, h', Bool.false_eq_true, ↓reduceIte]
    · rw [ite_eq_right hqs]
      have hne := summands_ne_nil hq0
      obtain ⟨R, hRdef⟩ : ∃ R, (summands q).getLast hne = R := ⟨_, rfl⟩
      have hpre : preT (info q).sums = (summands q).dropLast := preT_info q
      have hlast : lastT (info q).sums = R := by
        rw [lastT_info, List.getLast?_eq_some_getLast hne, hRdef]; rfl
      have hlastS : lastS (info q).sums = (info R).seq := by
        rw [lastS_coh (coh_sums q), hlast]
      have hsq : summands q = (summands q).dropLast ++ [R] := by
        rw [← hRdef]; exact (List.dropLast_concat_getLast hne).symm
      have hRq : R ∈ summands q := by rw [← hRdef]; exact List.getLast_mem hne
      have hR := summands_WNF q hqF R hRq
      have hqn : NFL ((summands q).dropLast ++ [R]) := by rw [← hsq]; exact nfl_summands hqF
      have hPF := wnf_ofSummands (nfl_append_left hqn)
      have heq : q = oadd (ofSummands (summands q).dropLast) R := eq_oadd_of_summands hqF hsq
      have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsq hR.2]; exact hqs
      have hlt : ∀ x, WNF x → Lt x R →
          WNF (oadd (ofSummands (summands q).dropLast) x) ∧
            Lt (oadd (ofSummands (summands q).dropLast) x) q := by
        intro x hx hxR
        refine ⟨wnf_oadd hPF hx, ?_⟩
        have := oadd_lt_oadd hPF hx hR.1 hxR
        rw [← heq] at this
        exact this
      -- 0 番目の項 `Ξ_m(pre ⊕ R[0])` は `p` 未満
      have hfirst : ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
            (lastS (info q).sums) .zero .zero).first = false ∧
          (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
            (lastS (info q).sums) .zero .zero).first ≠ p := by
        rw [hpre, hlast, hlastS]
        have hRi := hRinv R hRq
        cases hd : dom R with
        | zero =>
          have e := (dom_eq_zero_iff hR.1).mp hd
          rw [e] at hR
          cases hR.2
        | one => exact absurd ((dom_eq_one_iff hR.1).mp hd) hRns
        | omega =>
          have hN := hRi.1 hd
          have hr : (info R).seq.dom = .omega := hd
          rw [first_app_xi_nat hr (hN.props.nf 0)]
          obtain ⟨haF, haq⟩ := hlt _ (hN.props.nf 0) (hN.props.lt 0)
          exact ⟨hxa _ haF haq, hpX _⟩
        | big σ =>
          have hB := hRi.2 σ hd
          have hr : (info R).seq.dom = .big σ := hd
          have hσF := hB.props.σF
          have hστ : ltB σ (.Xi m q) = true := ltB_iff.mpr
            (lt_of_le_of_ltY hσF hR.1 hπ hB.σle (lt_of_le_of_ltY hR.1 hqF hπ (hsum_le _ hRq) hqπ))
          have hx0 := hB.props.nf .zero WNF.zero hB.props.pos
          rw [first_app_xi_big hr hστ hx0]
          obtain ⟨haF, haq⟩ := hlt _ hx0 (hB.props.lt .zero WNF.zero hB.props.pos)
          exact ⟨hxa _ haF haq, hpX _⟩
      have hsg : splitGtD p (info q).sums = none := by
        have hTW : (info q).sums.takeWhile (fun s => ltB p s.1) = [] := by
          refine takeWhile_eq_nil (fun x hx => ?_)
          have hx' := hmem x hx
          have hxF := hsumF _ hx'
          cases e : ltB p x.1 with
          | false => rfl
          | true =>
            exfalso
            exact Lt.asymmY hp hqF
              (lt_of_lt_of_leY hp hxF hqF (ltB_iff.mp e) (hsum_le _ hx')) hqp
        unfold splitGtD
        rw [hTW]
        rfl
      simp only [hfirst.1, Bool.false_eq_true, ↓reduceIte, hfirst.2, hsg]

/-! ### `Ψ_{Ξ_m(q)}(X'+1)`（`q < M_m`、`q < X'`） -/

theorem cs_succ_xi {m : Nat} {q X : Tm} (hX : WNF X) (hs : isSucc X = true)
    (hv : validR (.Xi m q) (pred X) = true) :
    cs (.Xi m q) X = mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (pred X))) := by
  have hX0 : X ≠ .zero := by
    intro e; rw [e] at hs; cases hs
  unfold cs cseq
  rw [ite_eq_right hX0, (lastS_dom_one_iff hX hX0).mpr hs]
  simp only [hv, ↓reduceIte]
  rfl

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < M_m`、`q < X'`）の列の不変量：`p = Ψ_{Ξ_m(q)}(X')` の上の `Ω` の塔 -/
theorem inv_psi_succ_xi_small {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hq : Lt q (.M m)) (hqX : Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → Inv u) : Inv (.Psi (.Xi m q) X) := by
  have hP := ht.psi
  have hπF := hP.piF
  have hXF := hP.aF
  have hm := hπF.xi.1
  have hqF := hπF.xi.2.1
  have hpF : WNF (.Psi (.Xi m q) (predT X)) :=
    psi_pred_wnf ht hs (fun n d e => by cases e; exact hqX)
  have hqp := lt_seed hpF hq
  have hXi : ∀ f, WNF (.Xi m f) → Lt (.Xi m f) (.Xi m q) →
      Lt (.Xi m f) (.Psi (.Xi m q) (predT X)) := fun f hf hfπ => xi_lt_seed hpF hqp hf hfπ
  obtain ⟨hpl, -⟩ := (baseOf_xi_iff m q _).mp (base_selfY hpF)
  have hv : validR (.Xi m q) (pred X) = true := ltB_iff.mpr hqX
  have hRinv : ∀ R, R ∈ summands q → Inv R := by
    intro R hR
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  have hcs : cs (.Xi m q) X = .tower (.Psi (.Xi m q) (predT X)) := by
    rw [cs_succ_xi hXF hs hv]
    exact mahloVK_small hπF hq hpF hpl hqp (fun a e => by cases e) hXi hRinv
  have hdom : dom (.Psi (.Xi m q) X) = .omega := by rw [dom_psi, hcs]; rfl
  have hf : ∀ n, fundNat (.Psi (.Xi m q) X) n = tower (.Psi (.Xi m q) (predT X)) (n + 1) := by
    intro n; rw [fundNat_psi, hcs]; rfl
  refine ⟨fun _ => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  refine natInv_tower ht hf hpF (lt_psi_psi_same.mpr (lt_predT hXF hs)) ?_ ?_ ?_ ?_ ?_
  · show max 1 (lev (succT (Tm.Psi (.Xi m q) (predT X)))) = m
    simp only [succT, lev]; exact Nat.max_eq_right hm
  · intro f hf hft
    obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := .Xi m q) (n := m) rfl).mp hft
    exact Or.inr (hXi f hf (lt_of_gtY hπF hf hgt))
  · intro ρ b hx hxt hlρ hnlt
    have hρF := hx.psi.piF
    rcases triY hρF hπF with h | rfl | h
    · exact absurd h hnlt
    · rcases le_pred_of_lt_succ hXF hs hx.psi.aF (lt_psi_psi_same.mp hxt) with e | h'
      · rw [e]; exact Or.inl rfl
      · exact Or.inr (lt_psi_psi_same.mpr h')
    · have hne : ρ ≠ .Xi m q := fun e => Lt.ne h e.symm
      have hl : lev ρ = lev (Tm.Xi m q) := hlρ
      exact Or.inr ((lt_psi_psi_gtT hl hne h).mpr ((lt_psi_psi_gtT hl hne h).mp hxt))
  · intro g d hg hg0 hd hC hnlt
    rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hXC, hXg⟩
    · exact absurd h1 hnlt
    · exact inC_psi_iff.mpr (Or.inr ⟨hπC, inC_of_succT (by rw [succT_predT hXF hs]; exact hXC),
        lt_transY (predT_WNF hXF hs) hXF hg (lt_predT hXF hs) hXg⟩)
  · intro v hv' hne hvt
    exact Or.inr (gap_psi_pred ht hs (fun e => by cases e) v hv' hne hvt)

/-! ### 残りの場合 -/

/-- `Ξ` への崩壊の後者のうち残りの場合：`q ≥ M_m`（`Ξ_m` の反復）か `q = X'`（底） -/
def PsiXiSuccRest : Prop :=
  ∀ n p X, WNF (.Psi (.Xi n p) X) → isSucc X = true → (¬ Lt p (.M n) ∨ ¬ Lt p (predT X)) →
    (∀ u, u.size < (Tm.Psi (.Xi n p) X).size → WNF u → Inv u) → Inv (.Psi (.Xi n p) X)

theorem psiXiSuccInv_of (hR : PsiXiSuccRest) : PsiXiSuccInv := by
  intro n p X ht hs ih
  by_cases h1 : Lt p (.M n)
  · by_cases h2 : Lt p (predT X)
    · exact inv_psi_succ_xi_small ht hs h1 h2 ih
    · exact hR n p X ht hs (Or.inr h2) ih
  · exact hR n p X ht hs (Or.inl h1) ih

end MahloOCF.FS
