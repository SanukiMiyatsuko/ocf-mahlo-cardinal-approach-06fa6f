import Mahlo.FS.PsiFam
import Mahlo.FS.Order

/-! 標準形の型 `NF` 上の基本列：`fund`・`dom` を `NF` に移し、FS の公理を示す。

全ての標準形の列の性質（`Props`）と Bachmann 性（`BachHyp`）から FS の公理を組み立てる（`fsOfProps`）。
列の性質は列の不変量（`inv_all`）から出る。崩壊 `Ψ_π(X)` の列の不変量のうち、`X = 0`・`Ω` への崩壊の後者
（`PsiMul`）・極限 `X` の素の近似（`PsiLim`）・`Ξ_m(q)`（`q < M_m`）への崩壊の後者（`PsiXi`）・目標そのものへの
対角化（`PsiDiag`）・外に足す型の塔（`PsiOut`）・`M_m` への対角化（`PsiK`・`PsiKO`）・`Ξ_m(q)` への崩壊の後者
（族の閉包：`q < X'` は `XiSucc`、底 `X' = q` は `XiFloor`）・外に足す型で族の閉包を添字にする場合（`PsiFam`）で、
全ての標準形の列の不変量が出る（`inv_of`）。残りの仮定は Bachmann 性だけ（`fsNF`）だが、今の基本列では
Bachmann 性は成り立たない（反例は `BachCE.lean`）。 -/

namespace MahloOCF.FS

open Tm

/-- Bachmann 性（項の上の形）：`t[n] < b < t` なら `t[n] ≤ b[0]` -/
def BachHyp : Prop :=
  ∀ t b n, WNF t → WNF b → dom t = .omega → Lt (fundNat t n) b → Lt b t →
    Le (fundNat t n) (fund b .zero)

/-- 標準形の共終数への持ち上げ -/
def liftCof : (c : Cof Tm) → (∀ σ, c = .big σ → WNF σ) → Cof NF
  | .zero, _ => .zero
  | .one, _ => .one
  | .omega, _ => .omega
  | .big σ, h => .big ⟨σ, h σ rfl⟩

theorem liftCof_zero {c : Cof Tm} {h : ∀ σ, c = .big σ → WNF σ} : liftCof c h = .zero ↔ c = .zero := by
  cases c <;> simp [liftCof]

theorem liftCof_one {c : Cof Tm} {h : ∀ σ, c = .big σ → WNF σ} : liftCof c h = .one ↔ c = .one := by
  cases c <;> simp [liftCof]

theorem liftCof_omega {c : Cof Tm} {h : ∀ σ, c = .big σ → WNF σ} : liftCof c h = .omega ↔ c = .omega := by
  cases c <;> simp [liftCof]

theorem liftCof_big {c : Cof Tm} {h : ∀ σ, c = .big σ → WNF σ} {σ : NF} :
    liftCof c h = .big σ ↔ c = .big σ.1 := by
  cases c with
  | big τ =>
    simp only [liftCof, Cof.big.injEq]
    constructor
    · intro e; rw [← e]
    · intro e; exact Subtype.ext e
  | _ => simp [liftCof]

section

variable (hψ : ∀ t, WNF t → Props t)
include hψ

theorem wnf_fund {t ξ : Tm} (ht : WNF t) (hξ : WNF ξ) : WNF (fund t ξ) := by
  have hP := hψ t ht
  rw [fund_eq]
  split
  · exact WNF.zero
  · exact wnf_pred ht
  · rename_i hd; exact (hP.1 hd).nf _
  · rename_i σ hd
    have hB := hP.2 σ hd
    split
    · rename_i h; exact hB.nf ξ hξ (ltB_iff.mp h)
    · exact hB.nf _ WNF.zero hB.pos

theorem wnf_dom_big {t σ : Tm} (ht : WNF t) (hd : dom t = .big σ) : WNF σ :=
  ((hψ t ht).2 σ hd).σF

/-- 基本列（`NF` 上） -/
def fundNF (a ξ : NF) : NF := ⟨fund a.1 ξ.1, wnf_fund hψ a.2 ξ.2⟩

/-- 共終数（`NF` 上） -/
def domNF (a : NF) : Cof NF := liftCof (dom a.1) (fun _ hd => wnf_dom_big hψ a.2 hd)

theorem domNF_zero {a : NF} : domNF hψ a = .zero ↔ dom a.1 = .zero := liftCof_zero

theorem domNF_one {a : NF} : domNF hψ a = .one ↔ dom a.1 = .one := liftCof_one

theorem domNF_omega {a : NF} : domNF hψ a = .omega ↔ dom a.1 = .omega := liftCof_omega

theorem domNF_big {a σ : NF} : domNF hψ a = .big σ ↔ dom a.1 = .big σ.1 := liftCof_big

end

theorem natOf_ofNatT (n : Nat) : natOf (ofNatT n) = n := by
  unfold natOf ofNatT
  rw [summands_mulNat (x := one) rfl]
  simp

theorem fund_omega {t : Tm} (h : dom t = .omega) (n : Nat) : fund t (ofNatT n) = fundNat t n := by
  rw [fund_eq, h]
  show fundNat t (natOf (ofNatT n)) = _
  rw [natOf_ofNatT]

theorem fund_big {t σ ξ : Tm} (h : dom t = .big σ) (hξ : Lt ξ σ) : fund t ξ = fundBig t ξ := by
  rw [fund_eq, h]
  show fundBig t (if ltB ξ σ = true then ξ else zero) = _
  rw [if_pos (ltB_iff.mpr hξ)]

/-- `NF` の `≤`（`Well_Order` から入るもの）と `Le` -/
theorem nf_le {a b : NF} : a ≤ b ↔ Le a.1 b.1 := by
  show (a < b ∨ a = b) ↔ _
  constructor
  · rintro (h | rfl)
    · exact Or.inr h
    · exact Or.inl rfl
  · rintro (h | h)
    · exact Or.inr (Subtype.ext h)
    · exact Or.inl h

theorem nf_lt {a b : NF} : a < b ↔ Lt a.1 b.1 := Iff.rfl

/-- 全ての標準形の列の性質と Bachmann 性から、`NF` は基本列の公理を満たす -/
@[reducible] def fsOfProps (hψ : ∀ t, WNF t → Props t) (hB : BachHyp) : FS NF where
  fund := fundNF hψ
  dom := domNF hψ
  Z := ⟨.zero, rfl⟩
  ofNat n := ⟨ofNatT n, wnf_ofNatT n⟩
  ofNat_zero := rfl
  ofNat_dom n := (domNF_one hψ).mpr (dom_ofNatT n)
  ofNat_fund n m := Subtype.ext (fund_ofNatT n m.1)
  zero_dom := (domNF_zero hψ).mpr rfl
  zero_unique a h := Subtype.ext ((dom_eq_zero_iff a.2).mp ((domNF_zero hψ).mp h))
  zero_fund n := rfl
  succ_md a n h := by
    have hd := (domNF_one hψ).mp h
    show Lt (fund a.1 n.1) a.1
    rw [fund_of_dom_one _ hd]
    exact pred_lt a.2 ((dom_eq_one_iff a.2).mp hd)
  succ_cof a n x h hx := by
    have hd := (domNF_one hψ).mp h
    rw [nf_le]
    show Le x.1 (fund a.1 n.1)
    rw [fund_of_dom_one _ hd]
    exact le_pred a.2 ((dom_eq_one_iff a.2).mp hd) x.2 hx
  omega_lt a n h := by
    have hd := (domNF_omega hψ).mp h
    show Lt (fund a.1 (ofNatT n)) a.1
    rw [fund_omega hd]
    exact ((hψ a.1 a.2).1 hd).lt n
  omega_mono a n h := by
    have hd := (domNF_omega hψ).mp h
    show Lt (fund a.1 (ofNatT n)) (fund a.1 (ofNatT (n + 1)))
    rw [fund_omega hd, fund_omega hd]
    exact ((hψ a.1 a.2).1 hd).mono n
  omega_bachmann a b n h h1 h2 := by
    have hd := (domNF_omega hψ).mp h
    rw [nf_le]
    show Le (fund a.1 (ofNatT n)) (fund b.1 (ofNatT 0))
    have h1' : Lt (fund a.1 (ofNatT n)) b.1 := h1
    rw [fund_omega hd] at h1' ⊢
    exact hB a.1 b.1 n a.2 b.2 hd h1' h2
  omega_cof a x h hx := by
    have hd := (domNF_omega hψ).mp h
    obtain ⟨n, hn⟩ := ((hψ a.1 a.2).1 hd).cof x.1 x.2 hx
    refine ⟨n, ?_⟩
    rw [nf_le]
    show Le x.1 (fund a.1 (ofNatT n))
    rw [fund_omega hd]
    exact hn
  big_lt a σ ξ h hξ := by
    have hd := (domNF_big hψ).mp h
    show Lt (fund a.1 ξ.1) a.1
    rw [fund_big hd hξ]
    exact ((hψ a.1 a.2).2 σ.1 hd).lt ξ.1 ξ.2 hξ
  big_mono a σ ξ η h hξη hησ := by
    have hd := (domNF_big hψ).mp h
    have hB' := (hψ a.1 a.2).2 σ.1 hd
    have hξσ : Lt ξ.1 σ.1 := lt_transY ξ.2 η.2 σ.2 hξη hησ
    show Lt (fund a.1 ξ.1) (fund a.1 η.1)
    rw [fund_big hd hξσ, fund_big hd hησ]
    exact hB'.mono ξ.1 η.1 ξ.2 η.2 hξη hησ
  big_cof a σ x h hx := by
    have hd := (domNF_big hψ).mp h
    obtain ⟨ξ, hξ, hξσ, hle⟩ := ((hψ a.1 a.2).2 σ.1 hd).cof x.1 x.2 hx
    refine ⟨⟨ξ, hξ⟩, hξσ, ?_⟩
    rw [nf_le]
    show Le x.1 (fund a.1 ξ)
    rw [fund_big hd hξσ]
    exact hle


/-- 全ての標準形の列の不変量 -/
theorem inv_of : ∀ t : Tm, WNF t → Inv t :=
  inv_all (psiInv_of (psiRestInv_of (psiDiagInv_of psiDiagFam_proof psiDiagM_proof)
    (psiXiSuccInv_of (psiXiSuccRest_of psiXiSuccFloor_proof))))

/-- Bachmann 性があれば、`NF` は基本列の公理を満たす -/
@[reducible] def fsNF (hB : BachHyp) : FS NF :=
  fsOfProps (fun t ht => (inv_of t ht).props) hB

end MahloOCF.FS

/-! `#print axioms` の出力を固定する検査。 -/

/-- info: 'MahloOCF.FS.fsNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.fsNF

/-- info: 'MahloOCF.FS.inv_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.inv_of
