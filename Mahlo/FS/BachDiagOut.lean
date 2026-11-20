import Mahlo.FS.BachDiagIn

/-! 外に足す型の対角化（`R` の共終数 `σ` が `M` でなく `π < σ`、`Ψ_π(X) < Ψ_σ(X)`）の `BInv`。

塔 `γ_{k+1} = Ψ_σ(pre ⊕ (c_σ ⊕ R[γ_k]))`（`γ_0` は `0` か `Ψ_σ(pre ⊕ (c_σ ⊕ R[0]))`）の添字は全て `0` か
`σ` の底より大きい主要項なので、`R` の区間の下界の移送が使える。`LBI (γ_k) (γ_{k+1})` を `k` についての
帰納法で示し（`σ` への崩壊の持ち上げ）、`π` への崩壊の持ち上げで列の梯子を得る。 -/

namespace MahloOCF.FS

open Tm

theorem binv_psi_diag_out {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big σ) (hRb : BInv R) (hπσ : Lt π σ) (hσM : ∀ m, σ ≠ .M m)
    (hT : Lt (.Psi π X) (.Psi σ X)) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hRi := (inv_of R hR.1).2 σ hRd
  have hRP := hRi.props
  have hσF := hRP.σF
  obtain ⟨-, c, cσ, γ, T⟩ := inv_psi_diag_out_full ht hsX hns hRd hRi hπσ hσM hT
  have hcS := mkApp_shape hπ T.hmk
  have hcσS := mkApp_shape hσF T.hmkσ
  have hxF : ∀ n, WNF (fundBig R (γ n)) := fun n => hRP.nf _ (T.γF n) (T.γσ n)
  -- `σ` への崩壊の持ち上げ
  have hlift : ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ → Lt ξ σ → LBI (fundBig R ξ) (fundBig R η) →
      WNF (.Psi σ (apx pre cσ (fundBig R ξ))) → WNF (.Psi σ (apx pre cσ (fundBig R η))) →
      LBI (.Psi σ (apx pre cσ (fundBig R ξ))) (.Psi σ (apx pre cσ (fundBig R η))) :=
    fun ξ η hξ hη hξη hησ hξσ hL hA hA' =>
      lbi_psi_apx T.hTF hsX T.adjσ.cF T.adjσ.cR hcσS (hRP.nf ξ hξ hξσ) (hRP.nf η hη hησ)
        (bigProps_mono_le hRP hξ hη hξη hησ) (hRP.lt η hη hησ) hL hA hA'
  -- `R` の区間の下界の移送
  have hRL : ∀ n, LBI (γ n) (γ (n + 1)) → LBI (fundBig R (γ n)) (fundBig R (γ (n + 1))) :=
    fun n h => hRb.big σ hRd (γ n) (γ (n + 1)) (T.γF n) (T.γF _) (Or.inr (T.γm n)) (T.γσ _)
      (T.adm n) h
  -- 塔の隣り合う項の区間の下界
  have hlad : ∀ n, LBI (γ n) (γ (n + 1)) ∧ LBI (fundBig R (γ n)) (fundBig R (γ (n + 1))) := by
    intro n
    induction n with
    | zero =>
      have h0 : LBI (γ 0) (γ (0 + 1)) := by
        rcases T.γ0 with e | e
        · rw [e]; exact lbi_zero _
        · have hA : WNF (.Psi σ (apx pre cσ (fundBig R .zero))) := by rw [← e]; exact T.γF 0
          have hA' : WNF (.Psi σ (apx pre cσ (fundBig R (γ 0)))) := by rw [← T.hcol 0]; exact T.γF _
          have hL0 := hRb.big σ hRd .zero (γ 0) WNF.zero (T.γF 0) (zero_le _) (T.γσ 0) (Or.inl rfl)
            (lbi_zero _)
          have h := hlift .zero (γ 0) WNF.zero (T.γF 0) (zero_le _) (T.γσ 0) hRP.pos hL0 hA hA'
          rw [← e] at h
          rw [T.hcol 0]
          exact h
      exact ⟨h0, hRL 0 h0⟩
    | succ n ih =>
      have h1 : LBI (γ (n + 1)) (γ (n + 1 + 1)) := by
        have hA := T.γF (n + 1)
        have hA' := T.γF (n + 1 + 1)
        rw [T.hcol n] at hA ⊢
        rw [T.hcol (n + 1)] at hA' ⊢
        exact hlift (γ n) (γ (n + 1)) (T.γF n) (T.γF _) (Or.inr (T.γm n)) (T.γσ _) (T.γσ n) ih.2 hA hA'
      exact ⟨h1, hRL (n + 1) h1⟩
  -- 列の梯子
  refine ⟨fun _ n => ?_, fun σ' hd => by rw [T.hdom] at hd; cases hd⟩
  have htN := (props_all _ ht).1 T.hdom
  have hA := htN.nf n
  have hA' := htN.nf (n + 1)
  rw [T.f] at hA hA' ⊢
  rw [T.f]
  exact lbi_psi_apx ht hsX T.adj.cF T.adj.cR hcS (hxF n) (hxF (n + 1))
    (Or.inr (hRP.mono _ _ (T.γF n) (T.γF _) (T.γm n) (T.γσ _))) (hRP.lt _ (T.γF _) (T.γσ _))
    (hlad n).2 hA hA'

/-! ### 対角化の場合分け -/

/-- 外に足す型の対角化で `Ψ_π(X) < Ψ_σ(X)` でない場合（添字は `σ` の族の閉包） -/
def PsiDiagFamBInv : Prop :=
  ∀ π X R σ pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big σ → BInv R → Lt π σ → (∀ m, σ ≠ .M m) → ¬ Lt (.Psi π X) (.Psi σ X) →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) → BInv (.Psi π X)

/-- `M_m` への対角化 -/
def PsiDiagMBInv : Prop :=
  ∀ π X R m pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big (.M m) → BInv R → ¬ Lt (.M m) π →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) → BInv (.Psi π X)

theorem psiDiagBInv_of (hF : PsiDiagFamBInv) (hM : PsiDiagMBInv) : PsiDiagBInv := by
  intro π X R σ pre ht hsX hns hRd hRb hσπ ih
  have hπ := ht.psi.piF
  have hX := ht.psi.aF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hσF := ((inv_of R hR.1).2 σ hRd).props.σF
  cases hσ : σ with
  | M m => rw [hσ] at hRd hσπ; exact hM π X R m pre ht hsX hns hRd hRb hσπ ih
  | _ =>
    all_goals
      have hσM : ∀ m, σ ≠ .M m := by intro m e; rw [hσ] at e; cases e
      rcases triY hσF hπ with h | e | h
      · exact absurd h hσπ
      · subst e; exact binv_psi_diag_in ht hsX hns hRd hRb
      · by_cases hT : Lt (.Psi π X) (.Psi σ X)
        · exact binv_psi_diag_out ht hsX hns hRd hRb h hσM hT
        · exact hF π X R σ pre ht hsX hns hRd hRb h hσM hT ih

/-- 外に足す型（族の閉包）・`M_m` への対角化・`Ξ` への崩壊の後者の場合から Bachmann 性 -/
theorem bachHyp_of_diag (hF : PsiDiagFamBInv) (hM : PsiDiagMBInv) (hS : PsiXiSuccBInv) : BachHyp :=
  bachHyp_of_rest (psiDiagBInv_of hF hM) hS

end MahloOCF.FS
