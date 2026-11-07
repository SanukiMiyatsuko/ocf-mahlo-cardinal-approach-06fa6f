import Mahlo.FS.Dom
import Mahlo.FS.CLem

/-! 基本列の性質（標準形・元の項より小さい・単調・共終）を項の形ごとに示す。

* `NatProps t`：共終数 `ω` の列の性質、`BigProps t σ`：共終数が正則項 `σ` の列の性質、`Props t`：その両方。
* 和 `a + b`・正則項（`M_n`・`Ω_0`・`Ω_{c+1}`・`Ξ_n(d)`）・`Ω_c`（`c` 極限）の列の性質は、部分項の性質から出る
  （`props_plus`・`props_reg`・`props_om`）。
* 崩壊 `Ψ_π(X)` の列の性質は仮定 `PsiProps` として受け取り、全ての標準形について `Props` を示す（`props_all`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 列の性質 -/

/-- 共終数 `ω` の列の性質 -/
structure NatProps (t : Tm) : Prop where
  nf : ∀ n, WNF (fundNat t n)
  lt : ∀ n, Lt (fundNat t n) t
  mono : ∀ n, Lt (fundNat t n) (fundNat t (n + 1))
  cof : ∀ x, WNF x → Lt x t → ∃ n, Le x (fundNat t n)

/-- 共終数が正則項 `σ` の列の性質 -/
structure BigProps (t σ : Tm) : Prop where
  σF : WNF σ
  pos : Lt .zero σ
  nf : ∀ ξ, WNF ξ → Lt ξ σ → WNF (fundBig t ξ)
  lt : ∀ ξ, WNF ξ → Lt ξ σ → Lt (fundBig t ξ) t
  mono : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt (fundBig t ξ) (fundBig t η)
  cof : ∀ x, WNF x → Lt x t → ∃ ξ, WNF ξ ∧ Lt ξ σ ∧ Le x (fundBig t ξ)

/-- 列の性質 -/
def Props (t : Tm) : Prop := (dom t = .omega → NatProps t) ∧ (∀ σ, dom t = .big σ → BigProps t σ)

/-! ### 補題 -/

/-- 標準形の和 `a + b` は `a ⊕ b` -/
theorem oadd_plus {a b : Tm} (h : WNF (.plus a b)) : oadd a b = .plus a b := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  obtain ⟨h', rest, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
  have hle : leB h' a = true := by simpa [leB] using WNF.plus_head h hs
  rw [oadd_eq_ofSummands ha hb hs, summands_principal hap, hs]
  simp only [List.takeWhile_cons, hle, ↓reduceIte, List.takeWhile_nil, List.cons_append, List.nil_append]
  show Tm.plus a (ofSummands (h' :: rest)) = _
  rw [← hs, ofSummands_summands b hb]

/-- `x < c`、`c` が後者でないなら `x + 1 < c` -/
theorem succT_lt_of_not_succ {x c : Tm} (hx : WNF x) (hc : WNF c) (hs : ¬ isSucc c = true)
    (h : Lt x c) : Lt (succT x) c := by
  rcases succT_leY hx hc h with e | e
  · exfalso
    have := isSucc_succT x
    rw [e] at this
    exact hs this
  · exact e

theorem succT_lt_succT {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : Lt (succT a) (succT b) :=
  lt_of_le_of_ltY (succT_WNF ha) hb (succT_WNF hb) (succT_leY ha hb h) (lt_succT b)

theorem le_oadd_leftW {a y : Tm} (ha : WNF a) (hy : WNF y) : Le a (oadd a y) := by
  by_cases hy0 : y = .zero
  · subst hy0; rw [oadd_zero]; exact Or.inl rfl
  · exact Or.inr (lt_oadd_left ha hy hy0)

theorem oadd_le_oadd {x y y' : Tm} (hx : WNF x) (hy : WNF y) (hy' : WNF y') (h : Le y y') :
    Le (oadd x y) (oadd x y') := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (oadd_lt_oadd hx hy hy' h)

theorem le_of_lt_or_eq {a b : Tm} (h : Lt a b ∨ a = b) : Le a b := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- `a + b` 未満の項は `a` 以下か、`a ⊕ y`（`y < b`） -/
theorem lt_plus_split {a b x : Tm} (h : WNF (.plus a b)) (hx : WNF x) (hlt : Lt x (.plus a b)) :
    Le x a ∨ ∃ y, WNF y ∧ Lt y b ∧ x = oadd a y := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  cases hxp : isPrincipal x
  · cases x with
    | zero => exact Or.inl (zero_le a)
    | plus h' r =>
      obtain ⟨hh, hr, hhp, hr0⟩ := hx.plus
      have e1 : cmpList (h' :: summands r) (a :: summands b) = .lt := by
        have := hlt; unfold Lt at this; rw [cmp_eq] at this; exact this
      rcases hc : cmpP h' a with _ | _ | _
      · exact Or.inl (Or.inr (lt_of_head_lt hap (summands_plus h' r) hc))
      · have e : h' = a := eq_of_cmpP_eqY hh ha hhp hap hc
        subst e
        rw [cmpList_cons_cons_eq _ _ hc] at e1
        refine Or.inr ⟨r, hr, ?_, (oadd_plus hx).symm⟩
        unfold Lt; rw [cmp_eq]; exact e1
      · rw [cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at e1
        cases e1
    | _ => simp [isPrincipal] at hxp
  · exact Or.inl ((lt_prin_plus_iffY hx hxp h).mp hlt)

/-! ### 和 -/

theorem natProps_plus {a b : Tm} (h : WNF (.plus a b)) (hb : NatProps b) : NatProps (.plus a b) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hlt => ?_⟩
  · rw [fundNat_plus]; exact wnf_oadd ha (hb.nf n)
  · rw [fundNat_plus, ← oadd_plus h]; exact oadd_lt_oadd ha (hb.nf n) hbF (hb.lt n)
  · rw [fundNat_plus, fundNat_plus]; exact oadd_lt_oadd ha (hb.nf n) (hb.nf (n + 1)) (hb.mono n)
  · rcases lt_plus_split h hx hlt with hle | ⟨y, hy, hyb, rfl⟩
    · refine ⟨0, ?_⟩
      rw [fundNat_plus]
      exact le_transY hx ha (wnf_oadd ha (hb.nf 0)) hle (le_oadd_leftW ha (hb.nf 0))
    · obtain ⟨n, hn⟩ := hb.cof y hy hyb
      exact ⟨n, by rw [fundNat_plus]; exact oadd_le_oadd ha hy (hb.nf n) hn⟩

theorem bigProps_plus {a b σ : Tm} (h : WNF (.plus a b)) (hb : BigProps b σ) : BigProps (.plus a b) σ := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  refine ⟨hb.σF, hb.pos, fun ξ hξ hξσ => ?_, fun ξ hξ hξσ => ?_, fun ξ η hξ hη hξη hησ => ?_,
    fun x hx hlt => ?_⟩
  · rw [fundBig_plus]; exact wnf_oadd ha (hb.nf ξ hξ hξσ)
  · rw [fundBig_plus, ← oadd_plus h]; exact oadd_lt_oadd ha (hb.nf ξ hξ hξσ) hbF (hb.lt ξ hξ hξσ)
  · rw [fundBig_plus, fundBig_plus]
    exact oadd_lt_oadd ha (hb.nf ξ hξ (lt_transY hξ hη hb.σF hξη hησ)) (hb.nf η hη hησ)
      (hb.mono ξ η hξ hη hξη hησ)
  · rcases lt_plus_split h hx hlt with hle | ⟨y, hy, hyb, rfl⟩
    · refine ⟨.zero, WNF.zero, hb.pos, ?_⟩
      rw [fundBig_plus]
      exact le_transY hx ha (wnf_oadd ha (hb.nf _ WNF.zero hb.pos)) hle
        (le_oadd_leftW ha (hb.nf _ WNF.zero hb.pos))
    · obtain ⟨ξ, hξ, hξσ, hle⟩ := hb.cof y hy hyb
      exact ⟨ξ, hξ, hξσ, by rw [fundBig_plus]; exact oadd_le_oadd ha hy (hb.nf ξ hξ hξσ) hle⟩

theorem props_plus {a b : Tm} (h : WNF (.plus a b)) (hb : Props b) : Props (.plus a b) :=
  ⟨fun hd => natProps_plus h (hb.1 (by rwa [dom_plus] at hd)),
    fun σ hd => bigProps_plus h (hb.2 σ (by rwa [dom_plus] at hd))⟩

/-! ### 正則項：`σ[ξ] = base σ ⊕ ξ` -/

end MahloOCF.FS

namespace MahloOCF.FS

open Tm

/-- 始点 `b` が `t` 未満の標準形で `t` が主要項なら、`t[ξ] = b ⊕ ξ` の列は共終数 `t` の性質を満たす -/
theorem bigProps_reg {t b : Tm} (ht : WNF t) (htp : isPrincipal t = true) (ht0 : t ≠ .zero)
    (hb : WNF b) (hbt : Lt b t) (hf : ∀ ξ, fundBig t ξ = oadd b ξ) : BigProps t t := by
  refine ⟨ht, zero_lt ht0, fun ξ hξ _ => ?_, fun ξ hξ hξt => ?_, fun ξ η hξ hη hξη _ => ?_,
    fun x hx hlt => ⟨x, hx, hlt, ?_⟩⟩
  · rw [hf]; exact wnf_oadd hb hξ
  · rw [hf]; exact oadd_lt_prin hb hξ htp hbt hξt
  · rw [hf, hf]; exact oadd_lt_oadd hb hξ hη hξη
  · rw [hf]; exact le_oadd_right hb hx

theorem dom_om_reg {c : Tm} (h : omReg c) : dom (.Om c) = .big (.Om c) := by
  rw [dom_om, if_pos h]

theorem dom_om_lim {c : Tm} (h : ¬ omReg c) : dom (.Om c) = dom c := by
  rw [dom_om, if_neg h]

theorem fundBig_om_reg {c : Tm} (h : omReg c) (ξ : Tm) : fundBig (.Om c) ξ = oadd (base (.Om c)) ξ := by
  rw [fundBig_om, if_pos h]

theorem fundBig_om_lim {c : Tm} (h : ¬ omReg c) (ξ : Tm) : fundBig (.Om c) ξ = .Om (sc (fundBig c ξ)) := by
  rw [fundBig_om, if_neg h]

/-- `M_n` の始点 `M_{n-1}`（`n = 1` なら 0） -/
theorem wnf_kTerm (m : Nat) : WNF (kTerm m) := by
  unfold kTerm
  split
  · exact WNF.zero
  · exact WNF.M' (by omega)

theorem kTerm_lt_M {n : Nat} (hn : 1 ≤ n) : Lt (kTerm (n - 1)) (.M n) := by
  unfold kTerm
  split
  · exact zero_lt (by intro e; cases e)
  · exact lt_of_lev_lt' (by simp only [lev]; omega)

theorem props_M {n : Nat} (h : WNF (.M n)) : Props (.M n) := by
  refine ⟨(fun hd => by rw [dom_M] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_M] at hd
  cases hd
  exact bigProps_reg h rfl (by intro e; cases e) (wnf_kTerm _) (kTerm_lt_M h.M) (fundBig_M n)

/-- `Ω_c`（`c = 0` か後者）の始点 `Ω_{c-1}` -/
theorem wnf_base_om {c : Tm} (h : WNF (.Om c)) : WNF (base (.Om c)) := by
  simp only [base]
  split
  · exact WNF.zero
  · have hp := wnf_pred h.om.1
    unfold omOf
    split
    · exact hp
    · rename_i hfix
      show isNF (.Om (pred c)) = true
      simp only [isNF, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hp, by simpa using hfix⟩

theorem base_om_lt {c : Tm} (h : WNF (.Om c)) (hs : omReg c) : Lt (base (.Om c)) (.Om c) := by
  have hc := h.om.1
  simp only [base]
  split
  · exact zero_lt (by intro e; cases e)
  · rename_i hc0
    have hsc : isSucc c = true := by
      rcases hs with e | e
      · exact absurd e hc0
      · exact e
    have hp := wnf_pred hc
    have hpc : Lt (pred c) c := pred_lt hc hsc
    unfold omOf
    split
    · exact lt_transY hp hc h hpc (lt_om_selfY h)
    · exact lt_om_iffG.mpr hpc

theorem props_om_reg {c : Tm} (h : WNF (.Om c)) (hs : omReg c) : Props (.Om c) := by
  refine ⟨(fun hd => by rw [dom_om_reg hs] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_om_reg hs] at hd
  cases hd
  exact bigProps_reg h rfl (by intro e; cases e) (wnf_base_om h) (base_om_lt h hs)
    (fundBig_om_reg hs)

/-- `Ξ_n(d)` の始点 `Ψ_{Ξ_n(d)}(d+1)` は `Ξ_n(d)` 未満（比較の規則だけで出る） -/
theorem psi_xi_lt_xi (n : Nat) (d a : Tm) : Lt (.Psi (.Xi n d) a) (.Xi n d) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_xi (pi := .Xi n d) (m := n) rfl, psiLtXi_eq, cmp_self]
  simp

/-- `Ξ_n(d)` の列（始点 `Ψ_{Ξ_n(d)}(d+1)` が標準形なら） -/
theorem props_xi {n : Nat} {d : Tm} (h : WNF (.Xi n d)) (hb : WNF (base (.Xi n d))) :
    Props (.Xi n d) := by
  refine ⟨(fun hd => by rw [dom_xi] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_xi] at hd
  cases hd
  exact bigProps_reg h rfl (by intro e; cases e) hb (psi_xi_lt_xi n d _) (fundBig_xi n d)

end MahloOCF.FS

namespace MahloOCF.FS

open Tm

/-! ### `Ω_c`（`c` 極限）：`Ω_c[ξ] = Ω_{c[ξ]+1}` -/

theorem nrY_shape : ∀ t : Tm, ∃ e, nrY t = .Om e
  | .zero => ⟨_, rfl⟩
  | .plus a _ => nrY_shape a
  | .Om a => ⟨_, rfl⟩
  | .M _ => ⟨_, rfl⟩
  | .Xi _ _ => ⟨_, rfl⟩
  | .Psi π β => by
    cases π with
    | Om c => exact ⟨c, rfl⟩
    | _ => exact ⟨_, rfl⟩

/-- `Ω_c`（`c` 極限）未満の項は、`c` 未満のある `e` について `Ω_e` 未満 -/
theorem lt_om_lim {c x : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hx : WNF x) (hlt : Lt x (.Om c)) :
    ∃ e, WNF e ∧ WNF (.Om e) ∧ Lt e c ∧ Lt x (.Om e) := by
  obtain ⟨hnF, hnR, hxn⟩ := nr_specY x hx
  obtain ⟨e, he⟩ := nrY_shape x
  have hle : Le (.Om e) (.Om c) := by rw [← he]; exact nr_le_omY x hx c h hlt
  rw [he] at hnF hnR hxn
  have heF := hnF.om.1
  rcases hle with e' | hlt'
  · exfalso
    cases e'
    apply hs
    rcases hnR with h1 | ⟨c', h1, h2⟩ | ⟨n, h1⟩ | ⟨n, p, h1⟩
    · cases h1; exact Or.inl rfl
    · cases h1; exact Or.inr h2
    · cases h1
    · cases h1
  · exact ⟨e, heF, hnF, lt_om_iffG.mp hlt', hxn⟩

theorem not_succ_of_not_omReg {c : Tm} (hs : ¬ omReg c) : ¬ isSucc c = true :=
  fun h => hs (Or.inr h)

/-- `x < Ω_e`、`e ≤ y` なら `x < Ω_{y+1}` -/
theorem lt_om_succ_of {x e y : Tm} (hx : WNF x) (heF : WNF e) (hOe : WNF (.Om e)) (hy : WNF y)
    (hxe : Lt x (.Om e)) (hey : Le e y) : Lt x (.Om (succT y)) :=
  lt_transY hx hOe (WNF.om_succT hy) hxe
    (lt_om_iffG.mpr (lt_of_le_of_ltY heF hy (succT_WNF hy) hey (lt_succT _)))

theorem natProps_om {c : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : NatProps c) :
    NatProps (.Om c) := by
  have hcF := h.om.1
  have hns := not_succ_of_not_omReg hs
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hlt => ?_⟩
  · rw [fundNat_om hs]; exact WNF.om_succT (hc.nf n)
  · rw [fundNat_om hs]
    exact lt_om_iffG.mpr (succT_lt_of_not_succ (hc.nf n) hcF hns (hc.lt n))
  · rw [fundNat_om hs, fundNat_om hs]
    exact lt_om_iffG.mpr (succT_lt_succT (hc.nf n) (hc.nf (n + 1)) (hc.mono n))
  · obtain ⟨e, heF, hOe, hec, hxe⟩ := lt_om_lim h hs hx hlt
    obtain ⟨n, hn⟩ := hc.cof e heF hec
    refine ⟨n, Or.inr ?_⟩
    rw [fundNat_om hs]
    exact lt_om_succ_of hx heF hOe (hc.nf n) hxe hn

theorem bigProps_om {c σ : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : BigProps c σ) :
    BigProps (.Om c) σ := by
  have hcF := h.om.1
  have hns := not_succ_of_not_omReg hs
  refine ⟨hc.σF, hc.pos, fun ξ hξ hξσ => ?_, fun ξ hξ hξσ => ?_, fun ξ η hξ hη hξη hησ => ?_,
    fun x hx hlt => ?_⟩
  · rw [fundBig_om_lim hs]; exact WNF.om_succT (hc.nf ξ hξ hξσ)
  · rw [fundBig_om_lim hs]
    exact lt_om_iffG.mpr (succT_lt_of_not_succ (hc.nf ξ hξ hξσ) hcF hns (hc.lt ξ hξ hξσ))
  · rw [fundBig_om_lim hs, fundBig_om_lim hs]
    have hξσ := lt_transY hξ hη hc.σF hξη hησ
    exact lt_om_iffG.mpr (succT_lt_succT (hc.nf ξ hξ hξσ) (hc.nf η hη hησ) (hc.mono ξ η hξ hη hξη hησ))
  · obtain ⟨e, heF, hOe, hec, hxe⟩ := lt_om_lim h hs hx hlt
    obtain ⟨ξ, hξ, hξσ, hle⟩ := hc.cof e heF hec
    refine ⟨ξ, hξ, hξσ, Or.inr ?_⟩
    rw [fundBig_om_lim hs]
    exact lt_om_succ_of hx heF hOe (hc.nf ξ hξ hξσ) hxe hle

theorem props_om_lim {c : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : Props c) : Props (.Om c) :=
  ⟨fun hd => natProps_om h hs (hc.1 (by rwa [dom_om_lim hs] at hd)),
    fun σ hd => bigProps_om h hs (hc.2 σ (by rwa [dom_om_lim hs] at hd))⟩

/-! ### 全ての標準形 -/

/-- 崩壊の場合の仮定：`Ψ_π(X)` の列の性質（真の部分項の性質を使ってよい）と、`Ξ_n(d)` の列の始点の標準形 -/
structure PsiProps : Prop where
  psi : ∀ π X, WNF (.Psi π X) → (∀ u, u.size < (Tm.Psi π X).size → WNF u → Props u) →
    Props (.Psi π X)
  xiBase : ∀ n d, WNF (.Xi n d) → WNF (base (.Xi n d))

/-- 崩壊の場合の仮定から、全ての標準形の列の性質 -/
theorem props_all (hψ : PsiProps) : ∀ t : Tm, WNF t → Props t := by
  intro t
  induction t using size_induction with
  | h t ih =>
  intro ht
  cases t with
  | zero => exact ⟨(fun hd => by cases hd), (fun σ hd => by cases hd)⟩
  | M n => exact props_M ht
  | plus a b =>
    obtain ⟨-, hb, -, -⟩ := ht.plus
    exact props_plus ht (ih b (by simp only [Tm.size]; omega) hb)
  | Om c =>
    by_cases hs : omReg c
    · exact props_om_reg ht hs
    · exact props_om_lim ht hs (ih c (by simp only [Tm.size]; omega) ht.om.1)
  | Xi n d => exact props_xi ht (hψ.xiBase n d ht)
  | Psi π X => exact hψ.psi π X ht (fun u hu huF => ih u hu huF)

end MahloOCF.FS
