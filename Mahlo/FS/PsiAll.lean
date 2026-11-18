import Mahlo.FS.PsiOut

/-! 対角化の場合分け：`PsiDiagInv` を、示した場合（目標そのもの・外に足す型の塔）と残りの場合
（外に足す型で `Ψ_σ(X) ≤ Ψ_π(X)`（`PsiDiagFam`）、`M_m` への対角化（`PsiDiagM`））に分ける。 -/

namespace MahloOCF.FS

open Tm

/-- 外に足す型の対角化で `Ψ_π(X) < Ψ_σ(X)` でない場合（添字は `σ` の族の閉包） -/
def PsiDiagFam : Prop :=
  ∀ π X R σ pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big σ → BigInv R σ → Lt π σ → (∀ m, σ ≠ .M m) → ¬ Lt (.Psi π X) (.Psi σ X) →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → Inv u) → Inv (.Psi π X)

/-- `M_m` への対角化 -/
def PsiDiagM : Prop :=
  ∀ π X R m pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big (.M m) → BigInv R (.M m) → ¬ Lt (.M m) π →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → Inv u) → Inv (.Psi π X)

/-- 対角化の場合分け -/
theorem psiDiagInv_of (hF : PsiDiagFam) (hM : PsiDiagM) : PsiDiagInv := by
  intro π X R σ pre ht hsX hns hRd hRi hσπ ih
  have hπ := ht.psi.piF
  have hσF := hRi.props.σF
  cases hσ : σ with
  | M m => rw [hσ] at hRd hRi hσπ; exact hM π X R m pre ht hsX hns hRd hRi hσπ ih
  | _ =>
    all_goals
      have hσM : ∀ m, σ ≠ .M m := by intro m e; rw [hσ] at e; cases e
      rcases triY hσF hπ with h | e | h
      · exact absurd h hσπ
      · subst e; exact inv_psi_diag_in ht hsX hns hRd hRi
      · by_cases hT : Lt (.Psi π X) (.Psi σ X)
        · exact inv_psi_diag_out ht hsX hns hRd hRi h hσM hT
        · exact hF π X R σ pre ht hsX hns hRd hRi h hσM hT ih

end MahloOCF.FS
