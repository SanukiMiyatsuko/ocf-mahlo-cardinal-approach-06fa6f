import Mahlo.WF.Fund
import Mahlo.FS.CLem

/-! 崩壊の候補 `Ψ_π(A)` との比較。

基本列の項 `Ψ_π(A_n)` が標準形であること（`A_n ∈ C(A_n, Ψ_π(A_n))`）を示すには、標準形と分かる前の
`Ψ_π(A_n)` と他の項を比べる必要がある。比較 `cmp` は標準形でない項にも定義されているので、`π` が標準形の
崩壊先、`A` が標準形であれば、`Ψ_π(A)` が標準形でなくても次が比較の規則だけで出る。

* `below_transfer`（移し替え）：`b` の部分項 `Ψ_π(Y)` について「`Y < B` なら `Y < A`」が成り立てば、
  `b < Ψ_π(B)` から `b < Ψ_π(A)`。特に `B ≤ A` なら単調（`below_mono`）。
* `below_lt_tgt`：`b < Ψ_π(A)` なら `b < π`。
* `below_cut`（切断）：`a < b`、`b < Ψ_π(A)` なら `a < Ψ_π(A)`。したがって `Ψ_π(A)` 未満の標準形の全体は
  下に閉じている（`cut_psi`）。 -/

namespace MahloOCF.FS

open Tm

/-- `Ω` の不動点 `X` と `Ω_e`（`X` の標準形を使わない形）：`Ω_e < X` ⟺ `e < X` -/
theorem lt_om_OF' {e X : Tm} (hX : IsOF X) (hX1 : 1 ≤ lev X) : Lt (.Om e) X ↔ Lt e X := by
  rcases Nat.lt_trichotomy (max 1 (lev e)) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' (by omega), fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

theorem wnf_omOf {x : Tm} (hx : WNF x) : WNF (omOf x) := by
  unfold omOf
  split
  · exact hx
  · rename_i hfix
    show isNF (.Om x) = true
    simp only [isNF, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hx, by simpa using hfix⟩

theorem _root_.MahloOCF.IsTgt.principal {π : Tm} (h : IsTgt π) : isPrincipal π = true := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> rfl

theorem _root_.MahloOCF.IsTgt.ne_zero {π : Tm} (h : IsTgt π) : π ≠ .zero := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> (intro e; cases e)

theorem not_node_plus {a b : Tm} : ¬ IsNode (.plus a b) := by
  rintro (⟨_, _, e⟩ | ⟨_, _, e⟩) <;> cases e

theorem not_node_om {a : Tm} : ¬ IsNode (.Om a) := by
  rintro (⟨_, _, e⟩ | ⟨_, _, e⟩) <;> cases e

theorem not_node_zero : ¬ IsNode .zero := by
  rintro (⟨_, _, e⟩ | ⟨_, _, e⟩) <;> cases e

/-- 節点が和の部分項なら、どれかの加数の部分項 -/
theorem node_mem_subs_ofSummands {v : Tm} (hv : IsNode v) :
    ∀ l : List Tm, v ∈ subs (ofSummands l) → ∃ s, s ∈ l ∧ v ∈ subs s
  | [], h => by
    simp only [ofSummands, subs, List.mem_singleton] at h
    subst h
    exact absurd hv not_node_zero
  | [a], h => ⟨a, List.mem_cons_self, h⟩
  | a :: b :: rest, h => by
    have h' : v ∈ subs (.plus a (ofSummands (b :: rest))) := h
    simp only [subs, List.mem_cons, List.mem_append] at h'
    rcases h' with e | h1 | h2
    · subst e; exact absurd hv not_node_plus
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨s, hs, hvs⟩ := node_mem_subs_ofSummands hv (b :: rest) h2
      exact ⟨s, List.mem_cons_of_mem _ hs, hvs⟩

/-- `Ω_{c-1}` の節点は `c` の節点 -/
theorem node_subs_omOf_predT {c v : Tm} (hs : isSucc c = true) (hv : IsNode v)
    (h : v ∈ subs (omOf (predT c))) : v ∈ subs c := by
  have hsub : v ∈ subs (predT c) := by
    unfold omOf at h
    split at h
    · exact h
    · simp only [subs, List.mem_cons] at h
      rcases h with e | h
      · subst e; exact absurd hv not_node_om
      · exact h
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  rw [predT_of_summands hys] at hsub
  obtain ⟨s, hs', hvs⟩ := node_mem_subs_ofSummands hv ys hsub
  exact subs_trans (mem_subs_of_mem_summands (by rw [hys]; exact List.mem_append_left _ hs')) hvs

/-- `Ω_{c-1} < Ω_c` -/
theorem omOf_predT_lt {c : Tm} (h : WNF (.Om c)) (hs : isSucc c = true) :
    Lt (omOf (predT c)) (.Om c) := by
  have hc := h.om.1
  have hp := predT_WNF hc hs
  have hpc : Lt (predT c) c := lt_predT hc hs
  unfold omOf
  split
  · exact lt_transY hp hc h hpc (lt_om_selfY h)
  · exact lt_om_iffG.mpr hpc

/-! ### 移し替え -/

/-- 移し替え：`b` の部分項 `Ψ_π(Y)` について「`Y < B` なら `Y < A`」が成り立てば、
    `b < Ψ_π(B)` から `b < Ψ_π(A)`（`Ψ_π(A)`・`Ψ_π(B)` は標準形でなくてよい） -/
theorem below_transfer {π A B : Tm} (hπ : WNF π) (hT : IsTgt π) : ∀ b : Tm, WNF b →
    (∀ Y, Tm.Psi π Y ∈ subs b → Lt Y B → Lt Y A) → Lt b (.Psi π B) → Lt b (.Psi π A) := by
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb hY hlt
  have hlev : lev b ≤ lev π := by have := lev_le_of_lt_gen hlt; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  -- `Ξ_m(δ)` の底の条件の移し替え
  have baseXi : ∀ m δ, (∀ v, v ∈ subs δ → v ∈ subs b) → (∀ v, v ∈ subs δ → v.size < b.size) →
      WNF δ → 1 ≤ m → lev π = m →
      baseOf (.Xi m δ) (.Psi π B) = true → baseOf (.Xi m δ) (.Psi π A) = true := by
    intro m δ hsub hsz hδ hm hlm hB
    obtain ⟨-, hC⟩ := (baseOf_xi_iff m δ _).mp hB
    refine (baseOf_xi_iff m δ _).mpr ⟨kTerm_lt_psi hm hlm, ?_⟩
    exact inC_mono_node δ δ _ δ _ hC (fun v hv _ hvlt =>
      ih v (hsz v hv) (hδ.of_mem_subs hv) (fun Y hYs => hY Y (hsub _ (subs_trans hv hYs))) hvlt)
      (fun _ _ _ h => h)
  cases b with
  | zero => exact zero_lt (by intro e; cases e)
  | plus a r =>
    obtain ⟨ha, -, -, -⟩ := hb.plus
    exact (lt_plus_prin_iffY hb rfl).mpr (ih a (by simp only [Tm.size]; omega) ha
      (fun Y hYs => hY Y (subs_plus_l hYs)) ((lt_plus_prin_iffY hb rfl).mp hlt))
  | M k => exact M_lt_psi (by simp only [lev] at hl; omega)
  | Om e =>
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_psiOmG.mp hlt)
    · exact lt_om_psiOmG.mpr (lt_om_psiOmG.mp hlt)
    · have hOF : ∀ Z, IsOF (.Psi (.Xi n p) Z) := fun Z => Or.inr ⟨n, p, Z, rfl⟩
      have h1 : ∀ Z, 1 ≤ lev (Tm.Psi (.Xi n p) Z) := fun Z => by simp only [lev]; exact hπ.xi.1
      exact (lt_om_OF' (hOF A) (h1 A)).mpr (ih e (by simp only [Tm.size]; omega) hb.om.1
        (fun Y hYs => hY Y (subs_om hYs)) ((lt_om_OF' (hOF B) (h1 B)).mp hlt))
  | Xi m f =>
    simp only [lev] at hl
    obtain ⟨hgt, hbase⟩ := (lt_xi_psi_iff (π := π) (γ := B) (f := f) (n := m) hl.symm).mp hlt
    refine (lt_xi_psi_iff (π := π) (γ := A) (f := f) (n := m) hl.symm).mpr ⟨hgt, ?_⟩
    exact baseXi m f (fun v hv => subs_xi hv) (fun v hv => by
      have := size_le_of_mem_subs hv; simp only [Tm.size]; omega) hb.xi.2.1 hb.xi.1 hl.symm hbase
  | Psi κ β =>
    have hP := hb.psi
    have hκF := hP.piF
    have hlκ : lev κ = lev π := by simpa [lev] using hl
    rcases triY hκF hπ with hκπ | rfl | hπκ
    · have hne : κ ≠ π := fun e => Lt.ne hκπ e
      have hnlt := Lt.asymmY hκF hπ hκπ
      have hB := (lt_psi_psi_ltT (β := β) (γ := B) hlκ hne hnlt).mp hlt
      refine (lt_psi_psi_ltT (β := β) (γ := A) hlκ hne hnlt).mpr ?_
      rcases hP.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hcF := hκF.om.1
        have hz := wnf_omOf (predT_WNF hcF hs)
        have hzs : (omOf (predT c)).size < (Tm.Psi (.Om c) β).size := by
          have := size_omOf_predT_lt hs
          simp only [Tm.size] at this ⊢
          omega
        refine (baseOf_om_succ hs).mpr (ih _ hzs hz (fun Y hYs => hY Y ?_)
          ((baseOf_om_succ hs).mp hB))
        exact subs_psi_p (subs_om (node_subs_omOf_predT hs (Or.inr ⟨π, Y, rfl⟩) hYs))
      · have hm := hκF.xi.1
        have hlm : lev π = m := by simp only [lev] at hlκ; exact hlκ.symm
        exact baseXi m δ (fun v hv => subs_psi_p (subs_xi hv)) (fun v hv => by
          have := size_le_of_mem_subs hv; simp only [Tm.size]; omega) hκF.xi.2.1 hm hlm hB
    · exact lt_psi_psi_same.mpr (hY β (self_mem_subs _) (lt_psi_psi_same.mp hlt))
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT (β := β) (γ := A) hlκ hne hπκ).mpr
        ((lt_psi_psi_gtT (β := β) (γ := B) hlκ hne hπκ).mp hlt)

/-- 単調性：`B ≤ A` なら `b < Ψ_π(B)` から `b < Ψ_π(A)` -/
theorem below_mono {π A B : Tm} (hπ : WNF π) (hT : IsTgt π) (hA : WNF A) (hB : WNF B)
    (hBA : Le B A) {b : Tm} (hb : WNF b) (h : Lt b (.Psi π B)) : Lt b (.Psi π A) :=
  below_transfer hπ hT b hb (fun _ hYs hYB =>
    lt_of_lt_of_leY (hb.of_mem_subs hYs).psi.aF hB hA hYB hBA) h

/-! ### `Ψ_π(A)` 未満なら `π` 未満 -/

theorem below_lt_tgt {π A : Tm} (hπ : WNF π) (hT : IsTgt π) : ∀ b : Tm, WNF b →
    Lt b (.Psi π A) → Lt b π := by
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb hlt
  have hlev : lev b ≤ lev π := by have := lev_le_of_lt_gen hlt; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' hl
  have hπp := hT.principal
  cases b with
  | zero => exact zero_lt hT.ne_zero
  | plus a r =>
    obtain ⟨ha, -, -, -⟩ := hb.plus
    exact (lt_plus_prin_iffY hb hπp).mpr (ih a (by simp only [Tm.size]; omega) ha
      ((lt_plus_prin_iffY hb rfl).mp hlt))
  | M k =>
    have hk := hb.M
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · simp only [lev] at hl; omega
    · have hl' : k + 1 = max 1 (lev c) := by simpa [lev] using hl
      have hne : c ≠ .M k := by
        intro e; subst e; simp [isSucc, summands, one] at hs
      rw [lt_principal_iff rfl rfl, (cmpP_M_om hl').1, if_neg hne]
    · have hl' : k + 1 = n := by simpa [lev] using hl
      exact (lt_principal_iff rfl rfl).mpr (cmpP_M_xi hl').1
  | Om e =>
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_iffG.mpr (lt_om_psiOmG.mp hlt)
    · exact lt_om_iffG.mpr (lt_om_psiOmG.mp hlt)
    · refine (lt_om_OFG (Or.inl ⟨n, p, rfl⟩) hπ).mpr (ih e (by simp only [Tm.size]; omega) hb.om.1 ?_)
      exact (lt_om_OF' (Or.inr ⟨n, p, A, rfl⟩) (by simp only [lev]; exact hπ.xi.1)).mp hlt
  | Xi m f =>
    simp only [lev] at hl
    obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := π) (γ := A) (f := f) (n := m) hl.symm).mp hlt
    exact lt_of_gtY hπ hb hgt
  | Psi κ β =>
    have hP := hb.psi
    have hκF := hP.piF
    have hlκ : lev κ = lev π := by simpa [lev] using hl
    rcases triY hκF hπ with hκπ | rfl | hπκ
    · exact lt_transY hb hκF hπ (lt_psi_targetY hb) hκπ
    · exact lt_psi_targetY hb
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      have hB := (lt_psi_psi_gtT (β := β) (γ := A) hlκ hne hπκ).mp hlt
      rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
      · exfalso
        have : baseOf (.Om .zero) (.Psi κ β) = true := (baseOf_om_zero _).mpr (by intro e; cases e)
        rw [this] at hB
        cases hB
      · have hz := wnf_omOf (predT_WNF hπ.om.1 hs)
        have hnlt : ¬ Lt (omOf (predT c)) (.Psi κ β) := fun h => by
          rw [(baseOf_om_succ hs).mpr h] at hB; cases hB
        exact lt_of_le_of_ltY hb hz hπ (le_of_not_ltY hz hb hnlt) (omOf_predT_lt hπ hs)
      · have hl' : lev κ = n := by simpa [lev] using hlκ
        exact (lt_psi_xiY (π := κ) (a := β) (b := p) (n := n) hl').mpr (Or.inr hB)

/-! ### 切断 -/

/-- 切断：`a < b`、`b < Ψ_π(A)` なら `a < Ψ_π(A)`（`Ψ_π(A)` は標準形でなくてよい） -/
theorem below_cut {π A : Tm} (hπ : WNF π) (hT : IsTgt π) (hA : WNF A) {b : Tm} (hb : WNF b)
    (hbD : Lt b (.Psi π A)) : ∀ a : Tm, WNF a → Lt a b → Lt a (.Psi π A) := by
  have hbπ : Lt b π := below_lt_tgt hπ hT b hb hbD
  intro a
  induction a using size_induction with
  | h a ih =>
  intro ha hab
  have hlev : lev a ≤ lev π := by
    have h1 := lev_le_of_lt_gen hab
    have h2 := lev_le_of_lt_gen hbD
    simp only [lev] at h2
    omega
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  have haπ : Lt a π := lt_transY ha hb hπ hab hbπ
  cases a with
  | zero => exact zero_lt (by intro e; cases e)
  | plus a1 a2 =>
    obtain ⟨ha1, -, -, -⟩ := ha.plus
    exact (lt_plus_prin_iffY ha rfl).mpr (ih a1 (by simp only [Tm.size]; omega) ha1
      (lt_transY ha1 ha hb (lt_plus_leftY ha) hab))
  | M k => exact M_lt_psi (by simp only [lev] at hl; omega)
  | Om e =>
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp haπ)
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp haπ)
    · refine (lt_om_OF' (Or.inr ⟨n, p, A, rfl⟩) (by simp only [lev]; exact hπ.xi.1)).mpr ?_
      exact ih e (by simp only [Tm.size]; omega) ha.om.1
        (lt_transY ha.om.1 ha hb (lt_om_selfY ha) hab)
  | Xi m f =>
    simp only [lev] at hl
    refine (lt_xi_psi_iff (π := π) (γ := A) (f := f) (n := m) hl.symm).mpr ⟨?_, ?_⟩
    · rw [swapY ha hπ]
      have : cmp (.Xi m f) π = .lt := haπ
      rw [this]; rfl
    · refine (baseOf_xi_iff m f _).mpr ⟨kTerm_lt_psi ha.xi.1 hl.symm, ?_⟩
      refine inC_mono_node f f _ f _ (xi_selfY ha) (fun v hv _ hvlt => ?_) (fun _ _ _ h => h)
      have hvF := ha.xi.2.1.of_mem_subs hv
      have := size_le_of_mem_subs hv
      exact ih v (by simp only [Tm.size]; omega) hvF (lt_transY hvF ha hb hvlt hab)
  | Psi κ β =>
    have hP := ha.psi
    have hκF := hP.piF
    have hlκ : lev κ = lev π := by simpa [lev] using hl
    rcases triY hκF hπ with hκπ | rfl | hπκ
    · have hne : κ ≠ π := fun e => Lt.ne hκπ e
      have hnlt := Lt.asymmY hκF hπ hκπ
      refine (lt_psi_psi_ltT (β := β) (γ := A) hlκ hne hnlt).mpr ?_
      have hself := base_selfY ha
      rcases hP.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hz := wnf_omOf (predT_WNF hκF.om.1 hs)
        have hza : Lt (omOf (predT c)) (.Psi (.Om c) β) := (baseOf_om_succ hs).mp hself
        have hzs : (omOf (predT c)).size < (Tm.Psi (.Om c) β).size := by
          have := size_omOf_predT_lt hs
          simp only [Tm.size] at this ⊢
          omega
        exact (baseOf_om_succ hs).mpr (ih _ hzs hz (lt_transY hz ha hb hza hab))
      · have hm := hκF.xi.1
        obtain ⟨-, hC⟩ := (baseOf_xi_iff m δ _).mp hself
        refine (baseOf_xi_iff m δ _).mpr
          ⟨kTerm_lt_psi hm (by simp only [lev] at hlκ; exact hlκ.symm), ?_⟩
        refine inC_mono_node δ δ _ δ _ hC (fun v hv _ hvlt => ?_) (fun _ _ _ h => h)
        have hvF := hκF.xi.2.1.of_mem_subs hv
        have := size_le_of_mem_subs hv
        exact ih v (by simp only [Tm.size]; omega) hvF (lt_transY hvF ha hb hvlt hab)
    · refine lt_psi_psi_same.mpr ?_
      rcases triY hP.aF hA with h | h | h
      · exact h
      · subst h
        exact absurd hbD (Lt.asymmY ha hb hab)
      · exfalso
        have hba : Lt b (.Psi κ β) := below_mono hπ hT hP.aF hA (Or.inr h) hb hbD
        exact Lt.asymmY ha hb hab hba
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT (β := β) (γ := A) hlκ hne hπκ).mpr
        (not_base_of_lt_tgtY ha hπ hT hlκ hπκ haπ)

/-- 切断：`d` 未満の標準形の全体は下に閉じている -/
def Cut (d : Tm) : Prop := ∀ a b, WNF a → WNF b → Lt a b → Lt b d → Lt a d

theorem Cut.of_wnf {d : Tm} (hd : WNF d) : Cut d :=
  fun _ _ ha hb h1 h2 => lt_transY ha hb hd h1 h2

/-- 崩壊の候補は切断 -/
theorem cut_psi {π A : Tm} (hπ : WNF π) (hT : IsTgt π) (hA : WNF A) : Cut (.Psi π A) :=
  fun a _ ha hb h1 h2 => below_cut hπ hT hA hb h2 a ha h1

theorem Cut.le {d a b : Tm} (hd : Cut d) (ha : WNF a) (hb : WNF b) (h1 : Le a b) (h2 : Lt b d) :
    Lt a d := by
  rcases h1 with rfl | h1
  · exact h2
  · exact hd a b ha hb h1 h2

/-- 切断 `d` 未満の標準形は `C(g, d)` に入る -/
theorem inC_of_lt_cut {d : Tm} (hd : Cut d) (g : Tm) : ∀ {x : Tm}, WNF x → Lt x d → inC x g d = true
  | .zero, _, _ => inC_zero _ _
  | .M _, _, _ => inC_M _ _ _
  | .plus a b, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, inC_of_lt_cut hd g ha (hd a _ ha hx (lt_plus_leftY hx) h),
      inC_of_lt_cut hd g hb (hd b _ hb hx (lt_plus_rightY hx) h)]
    rfl
  | .Om e, hx, h => by
    rw [inC_om]
    exact inC_of_lt_cut hd g hx.om.1 (hd e _ hx.om.1 hx (lt_om_selfY hx) h)
  | .Xi m a, _, h => inC_of_lt_node (Or.inl ⟨m, a, rfl⟩) h
  | .Psi p a, _, h => inC_of_lt_node (Or.inr ⟨p, a, rfl⟩) h

/-! ### 崩壊先の部分項 -/

theorem size_lt_of_mem_subs_ne {t s : Tm} (h : s ∈ subs t) (hne : s ≠ t) : s.size < t.size := by
  apply Nat.lt_of_not_le
  intro hle
  exact hne (eq_of_mem_subs_size h hle)

theorem ne_of_size_lt {v t : Tm} (h : v.size < t.size) : v ≠ t := fun e => by
  subst e; exact Nat.lt_irrefl _ h

/-- 加数は全体以下 -/
theorem le_of_mem_summands {c s : Tm} (hc : WNF c) (hs : s ∈ summands c) : Le s c := by
  have hsF := (summands_WNF c hc s hs).1
  obtain ⟨h', rest, e⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hs)
  have hhF := (summands_WNF c hc h' (by rw [e]; exact List.mem_cons_self)).1
  have hsh : Le s h' := by
    rw [e] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inl rfl
    · exact le_of_ne_gtY hsF hhF (le_head_of_nfl (by rw [← e]; exact nfl_summands hc) s hs)
  exact le_transY hsF hhF hc hsh (head_leY hc e)

/-- 崩壊先 `π` の真の部分項で `π` 未満のものは、どの `A` についても `Ψ_π(A)` 未満
    （`π` の部分項に `Ψ_π(·)` は現れないので、比較は `A` に依らない） -/
theorem sub_lt_psi {π : Tm} (hπ : WNF π) (hT : IsTgt π) (A : Tm) : ∀ u, u ∈ subs π → u ≠ π →
    WNF u → Lt u π → Lt u (.Psi π A) := by
  have hDp : isPrincipal (Tm.Psi π A) = true := rfl
  intro u
  induction u using size_induction with
  | h u ih =>
  intro hu hne huF hlt
  have husz : u.size < π.size := size_lt_of_mem_subs_ne hu hne
  have hsubIH : ∀ v, v ∈ subs u → v.size < u.size → WNF v → Lt v π → Lt v (.Psi π A) :=
    fun v hv hvs hvF hvπ =>
      ih v hvs (subs_trans hu hv) (ne_of_size_lt (by omega)) hvF hvπ
  have hlev : lev u ≤ lev π := lev_le_of_lt_gen hlt
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  -- `Ξ_m(f)`（`u` の部分項、`π` 未満）は `Ψ_π(A)` の底の条件を満たす
  have xiBase : ∀ m f, Tm.Xi m f ∈ subs u → WNF (.Xi m f) → Lt (.Xi m f) π → lev π = m →
      baseOf (.Xi m f) (.Psi π A) = true := by
    intro m f hfs hfF hfπ hlm
    refine (baseOf_xi_iff m f _).mpr ⟨kTerm_lt_psi hfF.xi.1 hlm, ?_⟩
    refine inC_mono_node f f (.Xi m f) f _ (xi_selfY hfF) (fun v hv _ hvlt => ?_) (fun _ _ _ h => h)
    have hvF := hfF.of_mem_subs (subs_xi hv)
    have h1 := size_le_of_mem_subs hv
    have h2 := size_le_of_mem_subs hfs
    exact hsubIH v (subs_trans hfs (subs_xi hv)) (by simp only [Tm.size] at h2; omega) hvF
      (lt_transY hvF hfF hπ hvlt hfπ)
  cases u with
  | zero => exact zero_lt (by intro e; cases e)
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := huF.plus
    exact (lt_plus_prin_iffY huF hDp).mpr (hsubIH a (subs_plus_l (self_mem_subs a))
      (by simp only [Tm.size]; omega) ha (lt_transY ha huF hπ (lt_plus_leftY huF) hlt))
  | M k => exact M_lt_psi (by simp only [lev] at hl; omega)
  | Om e =>
    have heF := huF.om.1
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp hlt)
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp hlt)
    · have heπ : Lt e (.Xi n p) := (lt_om_OFG (Or.inl ⟨n, p, rfl⟩) hπ).mp hlt
      exact (lt_om_OF' (Or.inr ⟨n, p, A, rfl⟩) (by simp only [lev]; exact hπ.xi.1)).mpr
        (hsubIH e (subs_om (self_mem_subs e)) (by simp only [Tm.size]; omega) heF heπ)
  | Xi m f =>
    simp only [lev] at hl
    have hgt : cmp π (.Xi m f) = .gt := by
      rw [swapY huF hπ]
      have : cmp (.Xi m f) π = .lt := hlt
      rw [this]; rfl
    exact (lt_xi_psi_iff (π := π) (γ := A) (f := f) (n := m) hl.symm).mpr
      ⟨hgt, xiBase m f (self_mem_subs _) huF hlt hl.symm⟩
  | Psi κ β =>
    have hP := huF.psi
    have hκF := hP.piF
    have hlκ : lev κ = lev π := by simpa [lev] using hl
    have hκsub : κ ∈ subs (Tm.Psi κ β) := subs_psi_p (self_mem_subs κ)
    rcases triY hκF hπ with hκπ | rfl | hπκ
    · have hne' : κ ≠ π := fun e => Lt.ne hκπ e
      have hnlt := Lt.asymmY hκF hπ hκπ
      refine (lt_psi_psi_ltT hlκ hne' hnlt).mpr ?_
      rcases hP.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · refine (baseOf_om_succ hs).mpr ?_
        have hcF := hκF.om.1
        have hpF := predT_WNF hcF hs
        have hpc : Lt (predT c) c := lt_predT hcF hs
        have hcκ : Lt c (.Om c) := lt_om_selfY hκF
        have hcπ : Lt c π := lt_transY hcF hκF hπ hcκ hκπ
        -- `c` の加数は `Ψ_π(A)` 未満
        have hsum : ∀ s, s ∈ summands c → Lt s (.Psi π A) := by
          intro s hs'
          have hsF := (summands_WNF c hcF s hs').1
          have hss : s ∈ subs c := mem_subs_of_mem_summands hs'
          have h1 := size_le_of_mem_subs hss
          exact hsubIH s (subs_psi_p (subs_om hss)) (by simp only [Tm.size]; omega) hsF
            (lt_of_le_of_ltY hsF hcF hπ (le_of_mem_summands hcF hs') hcπ)
        unfold omOf
        split
        · rename_i hfix
          exact hsum _ (predT_mem_summands hcF hs (fixed_principal hfix))
        · rcases hT with rfl | ⟨c'', rfl, hs''⟩ | ⟨n, p, rfl⟩
          · exact lt_om_psiOmG.mpr (lt_transY hpF hcF WNF.zero hpc (lt_om_iffG.mp hκπ))
          · exact lt_om_psiOmG.mpr (lt_transY hpF hcF hπ.om.1 hpc (lt_om_iffG.mp hκπ))
          · refine (lt_om_OF' (Or.inr ⟨n, p, A, rfl⟩) (by simp only [lev]; exact hπ.xi.1)).mpr ?_
            obtain ⟨ys, hys⟩ := summands_of_isSucc hs
            cases hy : ys with
            | nil =>
              have e : predT c = .zero := by rw [predT_of_summands hys, hy]; rfl
              rw [e]; exact zero_lt (by intro e; cases e)
            | cons y rest =>
              have hpred : summands (predT c) = y :: rest := by
                rw [summands_predT hcF hys, hy]
              have hyc : y ∈ summands c := by rw [hys, hy]; exact List.mem_cons_self
              exact lt_of_head_lt hDp hpred
                ((lt_principal_iff (summands_WNF c hcF y hyc).2 hDp).mp (hsum y hyc))
      · exact xiBase m δ hκsub hκF hκπ (by simp only [lev] at hlκ; exact hlκ.symm)
    · exfalso
      have := size_le_of_mem_subs hu
      simp only [Tm.size] at this
      omega
    · have hne' : κ ≠ π := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT hlκ hne' hπκ).mpr (not_base_of_lt_tgtY huF hπ hT hlκ hπκ hlt)

end MahloOCF.FS

/-- info: 'MahloOCF.FS.below_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.below_cut
