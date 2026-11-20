import Mahlo.FS.Inv

/-! 崩壊 `Ψ_π(X)` の列のうち `B·(n+2)` の形のもの。

* `Ψ_{Ω_c}(0)`（`c` は後者）：`B = Ω_{c-1}`（`inv_psi_zero`）。
* `Ψ_{Ω_c}(X'+1)`：`B = Ψ_{Ω_c}(X')`（`inv_psi_succ_om`）。

どちらも「`t` 未満の主要項は `B` 以下」（`hprin`）から共終性が出る（`natInv_mul`）。隙間
（`t` の真の部分項で `t` 未満のものは `B·2` 未満）は、部分項の形（`subs_sum_cases`）と大きさで示す。 -/

namespace MahloOCF.FS

open Tm

/-! ### 補題 -/

theorem omOf_principal (z : Tm) : isPrincipal (omOf z) = true := by
  unfold omOf
  split
  · rename_i h; exact fixed_principal h
  · rfl

theorem size_le_omOf (z : Tm) : z.size ≤ (omOf z).size := by
  unfold omOf
  split
  · exact Nat.le_refl _
  · simp only [Tm.size]; omega

/-- `z ≤ Ω_z` -/
theorem le_omOf {z : Tm} (hz : WNF z) : Le z (omOf z) := by
  have h := wnf_omOf hz
  by_cases hf : omegaFixed z = true
  · rw [omOf, ite_eq_left hf]; exact Or.inl rfl
  · rw [omOf, ite_eq_right hf] at h ⊢
    exact Or.inr (lt_om_selfY h)

/-- `e ≤ z` なら `Ω_e ≤ Ω_z`（右辺は項 `omOf z`） -/
theorem om_le_omOf {e z : Tm} (he : WNF (.Om e)) (hz : WNF z) (h : Le e z) :
    Le (.Om e) (omOf z) := by
  by_cases hf : omegaFixed z = true
  · rw [omOf, ite_eq_left hf]
    have hez : Lt e z := by
      rcases h with rfl | h
      · rw [he.om.2] at hf; cases hf
      · exact h
    rcases fixed_shape hz hf with ⟨m, rfl⟩ | hX
    · have hl := lev_le_of_lt_MY hz.M he.om.1 hez
      have hm := hz.M
      exact Or.inr (lt_of_lev_lt' (by simp only [lev]; omega))
    · exact Or.inr ((lt_om_OFG hX hz).mpr hez)
  · rw [omOf, ite_eq_right hf]
    exact le_om_of_leY h

theorem omOf_ne_zero (z : Tm) : omOf z ≠ .zero := by
  intro e
  have := omOf_principal z
  rw [e] at this
  cases this

/-- `1 < Ω_z` -/
theorem one_lt_omOf {z : Tm} (hz : WNF z) : Lt one (omOf z) := by
  have hB := wnf_omOf hz
  have hne : omOf z ≠ one := by
    unfold omOf
    split
    · rename_i hf
      intro e
      rw [e] at hf
      simp [omegaFixed, one, isXi] at hf
    · intro e; cases e
  rcases one_leY hB (omOf_ne_zero z) with e | h
  · exact absurd e.symm hne
  · exact h

/-- 加数が全て `B` 以下の項は `B·(長さ+1)` 未満 -/
theorem lt_mulNat_of_summands_le {B x : Tm} (hBp : isPrincipal B = true) (hx : WNF x)
    (hle : ∀ s, s ∈ summands x → Le s B) : Lt x (mulNat B ((summands x).length + 1)) := by
  have key : ∀ l : List Tm, (∀ s, s ∈ l → isPrincipal s = true ∧ Le s B) →
      cmpList l (List.replicate (l.length + 1) B) = .lt := by
    intro l
    induction l with
    | nil =>
      intro _
      show cmpList [] [B] = .lt
      exact cmpList_nil_cons _ _
    | cons s l ih =>
      intro h
      obtain ⟨hsp, hsB⟩ := h s List.mem_cons_self
      rw [List.length_cons, List.replicate_succ]
      rcases hsB with e | hlt
      · rw [e, cmpList_cons_cons_eq _ _ (cmpP_self B)]
        exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      · exact cmpList_head_lt _ _ ((lt_principal_iff hsp hBp).mp hlt)
  unfold Lt
  rw [cmp_eq, summands_mulNat hBp]
  exact key _ (fun s hs => ⟨(summands_WNF x hx s hs).2, hle s hs⟩)

/-- 項 `c` の部分項は、`c` の末尾の和か、加数の部分項 -/
theorem subs_sum_cases : ∀ {c v : Tm}, v ∈ subs c →
    (∃ L, summands c = L ++ summands v) ∨ ∃ s, s ∈ summands c ∧ v ∈ subs s
  | .zero, v, h => by
    simp only [subs, List.mem_singleton] at h
    subst h
    exact Or.inl ⟨[], rfl⟩
  | .plus a b, v, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Or.inl ⟨[], rfl⟩
    · exact Or.inr ⟨a, List.mem_cons_self, h⟩
    · rcases subs_sum_cases h with ⟨L, hL⟩ | ⟨s, hs, hv⟩
      · exact Or.inl ⟨a :: L, by rw [summands_plus, hL]; rfl⟩
      · exact Or.inr ⟨s, by rw [summands_plus]; exact List.mem_cons_of_mem _ hs, hv⟩
  | .M n, v, h => Or.inr ⟨.M n, by simp [summands], h⟩
  | .Om a, v, h => Or.inr ⟨.Om a, by simp [summands], h⟩
  | .Xi n a, v, h => Or.inr ⟨.Xi n a, by simp [summands], h⟩
  | .Psi p a, v, h => Or.inr ⟨.Psi p a, by simp [summands], h⟩

/-- 標準形の末尾の和は全体以下 -/
theorem le_of_tail {c v : Tm} {L : List Tm} (hc : WNF c) (hv : WNF v)
    (hL : summands c = L ++ summands v) : Le v c := by
  have h := le_ofSummands_prepend (L := L) (S := summands v) (by rw [← hL]; exact nfl_summands hc)
  rwa [← hL, ofSummands_summands v hv, ofSummands_summands c hc] at h

theorem mem_subs_one {v : Tm} (h : v ∈ subs one) : v = one ∨ v = .Om .zero ∨ v = .zero := by
  simpa [one, subs] using h

/-- 主要項 `B`（`1 < B`）について `B + 1 < B·2` -/
theorem succT_lt_mulNat_two {B : Tm} (hBp : isPrincipal B = true) (h1 : Lt one B) :
    Lt (succT B) (mulNat B 2) := by
  unfold Lt
  rw [cmp_eq, summands_succT, summands_mulNat hBp, summands_principal hBp]
  show cmpList [B, one] [B, B] = .lt
  rw [cmpList_cons_cons_eq _ _ (cmpP_self B)]
  exact cmpList_head_lt _ _ ((lt_principal_iff rfl hBp).mp h1)

theorem succT_le_succT {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) : Le (succT a) (succT b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (succT_lt_succT ha hb h)

/-! ### `t[n] = B·(n+2)` の列 -/

/-- `t[n] = B·(n+2)` の列の不変量：`t` 未満の主要項が `B` 以下なら共終 -/
theorem natInv_mul {t B : Tm} (ht : WNF t) (htp : isPrincipal t = true)
    (hf : ∀ n, fundNat t n = mulNat B (n + 2))
    (hB : WNF B) (hBp : isPrincipal B = true) (hBt : Lt B t)
    (hprin : ∀ x, WNF x → isPrincipal x = true → Lt x t → Le x B)
    (hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC t g d = true → ¬ Lt t d → inC B g d = true)
    (hgap : ∀ v, v ∈ subs t → v ≠ t → Lt v t → Lt v (mulNat B 2)) :
    NatInv t := by
  have hnf : ∀ n, WNF (mulNat B n) := wnf_mulNat hB hBp
  have hlt : ∀ n, Lt (mulNat B n) t := mulNat_lt_prin hBp htp hBt
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC => ?_, fun n v hv hne hvt => ?_, fun g d n _ _ _ hC => ?_⟩
  rotate_right
  · rw [hf] at hC ⊢
    unfold mulNat at hC
    have hBC : inC B g d = true :=
      (inC_ofSummands _).mp hC B (List.mem_replicate.mpr ⟨by omega, rfl⟩)
    exact inC_mulNat hBC _
  · rw [hf]; exact hnf _
  · rw [hf]; exact hlt _
  · rw [hf, hf]; exact mulNat_lt_mulNat hB hBp (by omega)
  · refine ⟨(summands x).length, ?_⟩
    rw [hf]
    have h1 : Lt x (mulNat B ((summands x).length + 1)) :=
      lt_mulNat_of_summands_le hBp hx (fun s hs => by
        have hsF := summands_WNF x hx s hs
        exact hprin s hsF.1 hsF.2 (lt_of_le_of_ltY hsF.1 hx ht (le_of_mem_summands hx hs) hxt))
    exact Or.inr (lt_transY hx (hnf _) (hnf _) h1 (mulNat_lt_mulNat hB hBp (by omega)))
  · rw [hf]
    unfold mulNat
    exact ofSummands_ne_zero (by rw [List.replicate_succ]; exact List.cons_ne_nil _ _)
      (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact hBp)
  · rw [hf]
    by_cases hd' : Lt t d
    · exact inC_of_lt_cut hd g (hnf _) (hd _ _ (hnf _) ht (hlt _) hd')
    · exact inC_mulNat (hub g d hg hg0 hd hC hd') _
  · rw [hf]
    have h2 := hgap v hv hne hvt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h2
    · exact lt_transY (ht.of_mem_subs hv) (hnf _) (hnf _) h2 (mulNat_lt_mulNat hB hBp (by omega))

/-! ### `Ψ_{Ω_c}(0)` -/

theorem cs_zero_om (c : Tm) :
    cs (Om c) zero = if c = zero then .one else .mul (omOf (pred c)) 2 := by
  unfold cs cseq
  rw [ite_eq_left rfl]

/-- `Ψ_{Ω_c}(0)`（`c` は後者）未満の主要項は `Ω_{c-1}` 以下 -/
theorem prin_le_psi_zero {c x : Tm} (h : WNF (.Psi (.Om c) .zero)) (hs : isSucc c = true)
    (hxF : WNF x) (hxp : isPrincipal x = true) (hx : Lt x (.Psi (.Om c) .zero)) :
    Le x (omOf (predT c)) := by
  have hπF := h.psi.piF
  have hcF := hπF.om.1
  have hpF := predT_WNF hcF hs
  have hBF := wnf_omOf hpF
  have hxπ : Lt x (.Om c) := lt_transY hxF h hπF hx (lt_psi_targetY h)
  have hnr := nr_le_omY x hxF c hπF hxπ
  -- `Ω_{y+1} ≤ Ω_c` なら `y ≤ c - 1`
  have key : ∀ y, WNF y → Le (.Om (succT y)) (.Om c) → Le y (predT c) := by
    intro y hy hle
    have hsy := succT_WNF hy
    have h1 : Le (succT y) c := by
      rcases hle with e | hlt
      · cases e; exact Or.inl rfl
      · exact Or.inr (lt_om_iffG.mp hlt)
    exact le_pred_of_lt_succ hcF hs hy (lt_of_lt_of_leY hy hsy hcF (lt_succT y) h1)
  cases x with
  | zero => cases hxp
  | plus a b => cases hxp
  | M k => exact le_transY hxF hpF hBF (key _ hxF hnr) (le_omOf hpF)
  | Xi m f => exact le_transY hxF hpF hBF (key _ hxF hnr) (le_omOf hpF)
  | Om e => exact om_le_omOf hxF hpF (key e hxF.om.1 hnr)
  | Psi κ β =>
    rcases hxF.psi_shape with rfl | ⟨d', rfl, hs'⟩ | ⟨n, p, rfl⟩
    · exact Or.inr (lt_of_lt_of_leY hxF WNF.om_zero hBF (lt_psi_targetY hxF)
        (om_le_omOf WNF.om_zero hpF (zero_le _)))
    · have hd'F := hxF.psi.piF.om.1
      have hle : Le (.Om d') (.Om c) := hnr
      rcases hle with e | hlt
      · cases e
        exact absurd (lt_psi_psi_same.mp hx) (not_lt_zero β)
      · have hd'p : Le d' (predT c) := le_pred_of_lt_succ hcF hs hd'F (lt_om_iffG.mp hlt)
        exact Or.inr (lt_of_lt_of_leY hxF hxF.psi.piF hBF (lt_psi_targetY hxF)
          (om_le_omOf hxF.psi.piF hpF hd'p))
    · exact le_transY hxF hpF hBF (key _ hxF hnr) (le_omOf hpF)

/-- `Ψ_{Ω_c}(0)` の列の不変量 -/
theorem inv_psi_zero {c : Tm} (h : WNF (.Psi (.Om c) .zero)) : Inv (.Psi (.Om c) .zero) := by
  rcases h.psi_shape with e | ⟨c', e, hs⟩ | ⟨n, p, e⟩
  · cases e
    have hd1 : dom (.Psi (.Om .zero) .zero) = .one := dom_one_iff_psi.mpr ⟨rfl, rfl⟩
    exact ⟨(fun hd => by rw [hd1] at hd; cases hd), (fun σ hd => by rw [hd1] at hd; cases hd)⟩
  · cases e
    have hc0 : c ≠ .zero := by
      intro e; rw [e] at hs; cases hs
    have hcs : cs (Om c) zero = .mul (omOf (pred c)) 2 := by rw [cs_zero_om, ite_eq_right hc0]
    have hdom : dom (.Psi (.Om c) .zero) = .omega := by rw [dom_psi, hcs]; rfl
    have hf : ∀ n, fundNat (.Psi (.Om c) .zero) n = mulNat (omOf (predT c)) (n + 2) := by
      intro n; rw [fundNat_psi, hcs]; rfl
    refine ⟨fun _ => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
    have hπF := h.psi.piF
    have hcF := hπF.om.1
    have hpF := predT_WNF hcF hs
    have hB := wnf_omOf hpF
    have hBp := omOf_principal (predT c)
    have hBt : Lt (omOf (predT c)) (.Psi (.Om c) .zero) := (baseOf_om_succ hs).mp (base_selfY h)
    have hprin : ∀ x, WNF x → isPrincipal x = true → Lt x (.Psi (.Om c) .zero) →
        Le x (omOf (predT c)) := fun x hx hxp hlt => prin_le_psi_zero h hs hx hxp hlt
    have hB2 : Lt (omOf (predT c)) (mulNat (omOf (predT c)) 2) :=
      mulNat_lt_mulNat hB hBp (n := 1) (by omega)
    have hB2F := wnf_mulNat hB hBp 2
    refine natInv_mul h rfl hf hB hBp hBt hprin (fun g d' hg hg0 hd hC hnlt => ?_)
      (fun v hv hne hvt => ?_)
    · rcases inC_psi_iff.mp hC with hlt | ⟨hπC, -, -⟩
      · exact absurd hlt hnlt
      · rw [inC_om] at hπC
        have hpC : inC (predT c) g d' = true :=
          inC_of_succT (by rw [succT_predT hcF hs]; exact hπC)
        unfold omOf
        split
        · exact hpC
        · rw [inC_om]; exact hpC
    · have hvF := h.of_mem_subs hv
      -- 主要項か `0` で `t` 未満なら `B` 以下
      have hsmall : ∀ w, WNF w → (isPrincipal w = true ∨ w = .zero) → Lt w (.Psi (.Om c) .zero) →
          Lt w (mulNat (omOf (predT c)) 2) := by
        intro w hw hwp hwt
        rcases hwp with hwp | rfl
        · exact lt_of_le_of_ltY hw hB hB2F (hprin w hw hwp hwt) hB2
        · exact zero_lt (Lt.ne_zero hB2)
      -- `c - 1` の部分項で `t` 未満のものは `B` 以下
      have hle1 : ∀ w, w ∈ subs (predT c) → WNF w → Lt w (.Psi (.Om c) .zero) →
          Le w (omOf (predT c)) := by
        intro w hws hw hwt
        cases hsw : summands w with
        | nil => rw [eq_zero_of_summands_nil hsw]; exact zero_le _
        | cons h' r =>
          have hh := summands_WNF w hw h' (by rw [hsw]; exact List.mem_cons_self)
          have hh't : Lt h' (.Psi (.Om c) .zero) :=
            lt_of_le_of_ltY hh.1 hw h (head_leY hw hsw) hwt
          rcases hprin h' hh.1 hh.2 hh't with e | hlt
          · have hBw : omOf (predT c) ∈ subs w := by
              rw [← e]; exact mem_subs_of_mem_summands (by rw [hsw]; exact List.mem_cons_self)
            have h1 := size_le_of_mem_subs hws
            have h2 := size_le_omOf (predT c)
            exact Or.inl (eq_of_mem_subs_size hBw (by omega)).symm
          · exact Or.inr (lt_of_head_lt hBp hsw ((lt_principal_iff hh.2 hBp).mp hlt))
      simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with e | (e | hvc) | e
      · exact absurd e hne
      · rw [e] at hvt
        exact absurd hvt (Lt.asymmY h hπF (lt_psi_targetY h))
      · rcases subs_sum_cases hvc with ⟨L, hL⟩ | ⟨s, hs', hvs⟩
        · -- 末尾の和：`v ≤ c = (c-1)+1 ≤ B + 1 < B·2`
          have hvc' : Le v c := le_of_tail hcF hvF hL
          have hcB : Lt c (mulNat (omOf (predT c)) 2) := by
            have h1 : Le (succT (predT c)) (succT (omOf (predT c))) :=
              succT_le_succT hpF hB (le_omOf hpF)
            rw [succT_predT hcF hs] at h1
            exact lt_of_le_of_ltY hcF (succT_WNF hB) hB2F h1
              (succT_lt_mulNat_two hBp (one_lt_omOf hpF))
          exact lt_of_le_of_ltY hvF hcF hB2F hvc' hcB
        · obtain ⟨ys, hys⟩ := summands_of_isSucc hs
          rw [hys] at hs'
          rcases List.mem_append.mp hs' with hs1 | hs1
          · have hsp : s ∈ subs (predT c) :=
              mem_subs_of_mem_summands (by rw [summands_predT hcF hys]; exact hs1)
            exact lt_of_le_of_ltY hvF hB hB2F (hle1 v (subs_trans hsp hvs) hvF hvt) hB2
          · rw [List.mem_singleton.mp hs1] at hvs
            rcases mem_subs_one hvs with e | e | e
            · exact hsmall v hvF (Or.inl (by rw [e]; rfl)) hvt
            · exact hsmall v hvF (Or.inl (by rw [e]; rfl)) hvt
            · exact hsmall v hvF (Or.inr e) hvt
      · rw [e]; exact zero_lt (Lt.ne_zero hB2)
  · cases e

/-! ### `Ψ_{Ω_d}(X'+1)` -/

theorem lastT_mem {X : Tm} (hX0 : X ≠ .zero) : lastT (info X).sums ∈ summands X := by
  rw [lastT_info]
  have hne := summands_ne_nil hX0
  rw [List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

theorem lastS_dom (X : Tm) : (lastS (info X).sums).dom = dom (lastT (info X).sums) := by
  rw [lastS_coh (coh_sums X)]; rfl

/-- 最後の加数の共終数が後者 ⟺ `X` が後者 -/
theorem lastS_dom_one_iff {X : Tm} (hX : WNF X) (hX0 : X ≠ .zero) :
    (lastS (info X).sums).dom = .one ↔ isSucc X = true := by
  have hm := summands_WNF X hX _ (lastT_mem hX0)
  rw [lastS_dom, dom_eq_one_iff hm.1, isSucc_principal hm.2, lastT_info]
  unfold isSucc
  have hne := summands_ne_nil hX0
  rw [List.getLast?_eq_some_getLast hne]
  simp

theorem cs_succ_om {d X : Tm} (hX : WNF X) (hs : isSucc X = true) :
    cs (Om d) X = .mul (Psi (Om d) (pred X)) 2 := by
  have hX0 : X ≠ .zero := by
    intro e; rw [e] at hs; cases hs
  unfold cs cseq
  rw [ite_eq_right hX0, (lastS_dom_one_iff hX hX0).mpr hs]
  simp [validR, argR?]

/-- `Ψ_{Ω_d}(X'+1)` の列の不変量 -/
theorem inv_psi_succ_om {d X : Tm} (h : WNF (.Psi (.Om d) X)) (hs : isSucc X = true) :
    Inv (.Psi (.Om d) X) := by
  have hP := h.psi
  have hπF := hP.piF
  have hXF := hP.aF
  have hT := hP.tgt
  have hpF := predT_WNF hXF hs
  have hcs := cs_succ_om (d := d) hXF hs
  have hdom : dom (.Psi (.Om d) X) = .omega := by rw [dom_psi, hcs]; rfl
  have hf : ∀ n, fundNat (.Psi (.Om d) X) n = mulNat (.Psi (.Om d) (predT X)) (n + 2) := by
    intro n; rw [fundNat_psi, hcs]; rfl
  refine ⟨fun _ => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  have hB : WNF (.Psi (.Om d) (predT X)) := psi_pred_WNF h hs
  have hBt : Lt (.Psi (.Om d) (predT X)) (.Psi (.Om d) X) :=
    lt_psi_psi_same.mpr (lt_predT hXF hs)
  have hprin : ∀ x, WNF x → isPrincipal x = true → Lt x (.Psi (.Om d) X) →
      Le x (.Psi (.Om d) (predT X)) := fun x hx hxp hlt => prin_le_psi_pred h hs hx hxp hlt
  have hB2 : Lt (.Psi (.Om d) (predT X)) (mulNat (.Psi (.Om d) (predT X)) 2) :=
    mulNat_lt_mulNat hB rfl (n := 1) (by omega)
  have hB2F := wnf_mulNat hB rfl 2
  refine natInv_mul h rfl hf hB rfl hBt hprin (fun g d' hg hg0 hd hC hnlt => ?_)
    (fun v hv hne hvt => ?_)
  · rcases inC_psi_iff.mp hC with hlt | ⟨hπC, hXC, hXg⟩
    · exact absurd hlt hnlt
    · refine inC_psi_iff.mpr (Or.inr ⟨hπC, inC_of_succT (by rw [succT_predT hXF hs]; exact hXC), ?_⟩)
      exact lt_transY hpF hXF hg (lt_predT hXF hs) hXg
  · have hvF := h.of_mem_subs hv
    have hsmall : ∀ w, WNF w → (isPrincipal w = true ∨ w = .zero) → Lt w (.Psi (.Om d) X) →
        Lt w (mulNat (.Psi (.Om d) (predT X)) 2) := by
      intro w hw hwp hwt
      rcases hwp with hwp | rfl
      · exact lt_of_le_of_ltY hw hB hB2F (hprin w hw hwp hwt) hB2
      · exact zero_lt (Lt.ne_zero hB2)
    simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | hvπ | hvX
    · exact absurd e hne
    · -- 崩壊先の部分項
      have hvπ' : v ∈ subs (Tm.Om d) := by simpa [subs] using hvπ
      have hlt : Lt v (.Om d) := lt_transY hvF h hπF hvt (lt_psi_targetY h)
      exact lt_transY hvF hB hB2F (sub_lt_psi hπF hT (predT X) v hvπ' (Lt.ne hlt) hvF hlt) hB2
    · by_cases hmem : Tm.Psi (.Om d) (predT X) ∈ subs v
      · -- `Ψ_π(X') ∈ subs (X'+1)` となるのは `Ψ_π(X') = 1`、`X = 1` のときだけ
        have hw : Tm.Psi (.Om d) (predT X) ∈ subs X := subs_trans hvX hmem
        obtain ⟨ys, hys⟩ := summands_of_isSucc hs
        have hszp : ∀ s, s ∈ ys → Tm.Psi (.Om d) (predT X) ∈ subs s → False := by
          intro s hs1 hws
          have hsp : s ∈ subs (predT X) :=
            mem_subs_of_mem_summands (by rw [summands_predT hXF hys]; exact hs1)
          have h1 := size_le_of_mem_subs hws
          have h2 := size_le_of_mem_subs hsp
          simp only [Tm.size] at h1
          omega
        have hone : Tm.Psi (.Om d) (predT X) = one := by
          rcases subs_sum_cases hw with ⟨L, hL⟩ | ⟨s, hs', hws⟩
          · rw [hys] at hL
            have hL' : ys ++ [one] = L ++ [Tm.Psi (.Om d) (predT X)] := hL
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
        have hp0 : predT X = .zero :=
          (Tm.Psi.inj (show Tm.Psi (.Om d) (predT X) = .Psi (.Om .zero) .zero from hone)).2
        have hX1 : X = one := by
          rw [← succT_predT hXF hs, hp0]; rfl
        rw [hX1] at hvX
        rcases mem_subs_one hvX with e | e | e
        · exact hsmall v hvF (Or.inl (by rw [e]; rfl)) hvt
        · exact hsmall v hvF (Or.inl (by rw [e]; rfl)) hvt
        · exact hsmall v hvF (Or.inr e) hvt
      · have hvB : Lt v (.Psi (.Om d) (predT X)) :=
          below_transfer hπF hT v hvF (fun Y hYs hYX =>
            lt_pred_of_lt_succ hXF hs (hvF.of_mem_subs hYs).psi.aF hYX
              (fun e => hmem (by rw [← e]; exact hYs))) hvt
        exact lt_transY hvF hB hB2F hvB hB2

/-! ### 残りの場合 -/

/-- 崩壊 `Ψ_π(X)` の列の不変量のうち、`X ≠ 0` で、後者なら `π = Ξ_n(p)` の場合 -/
def PsiRestInv : Prop :=
  ∀ π X, WNF (.Psi π X) → X ≠ .zero → (isSucc X = true → ∃ n p, π = .Xi n p) →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → Inv u) → Inv (.Psi π X)

theorem psiInv_of (hR : PsiRestInv) : PsiInv := by
  intro π X ht ih
  by_cases hX0 : X = .zero
  · subst hX0
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact inv_psi_zero ht
    · exact inv_psi_zero ht
    · exact absurd (ht.psi.act n p rfl) (not_lt_zero p)
  · by_cases hs : isSucc X = true
    · rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
      · exact inv_psi_succ_om ht hs
      · exact inv_psi_succ_om ht hs
      · exact hR _ _ ht hX0 (fun _ => ⟨n, p, rfl⟩) ih
    · exact hR _ _ ht hX0 (fun hs' => absurd hs' hs) ih

end MahloOCF.FS
