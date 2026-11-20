import Mahlo.FS.BachMain

/-! 崩壊の簡単な場合の `BInv`：`Ψ_{Ω_c}(0)`（`Ω_{c-1}·ω`）と `Ψ_{Ω_d}(X'+1)`（`Ψ_{Ω_d}(X')·ω`）。列は `B·(n+2)` で、
隣り合う項の区間の下界は主要項 `B` を前に足すこと（`lbi_oadd_prin`）から出る（`lbi_mulNat`）。 -/

namespace MahloOCF.FS

open Tm

/-- `B ⊕ B·k = B·(k+1)` -/
theorem oadd_mulNat {B : Tm} (hB : WNF B) (hBp : isPrincipal B = true) (k : Nat) :
    oadd B (mulNat B k) = mulNat B (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    have hs : summands (mulNat B (k + 1)) = B :: List.replicate k B := by
      rw [summands_mulNat hBp]; rfl
    rw [oadd_eq_ofSummands hB (wnf_mulNat hB hBp _) hs, summands_principal hBp]
    have hle : leB B B = true := le_leB (Or.inl rfl)
    simp only [List.takeWhile_cons, hle, ↓reduceIte, List.takeWhile_nil, List.cons_append,
      List.nil_append]
    rw [summands_mulNat hBp]
    rfl

/-- `B·k` と `B·(k+1)` の区間の下界 -/
theorem lbi_mulNat {B : Tm} (hB : WNF B) (hBp : isPrincipal B = true) :
    ∀ k, LBI (mulNat B k) (mulNat B (k + 1)) := by
  intro k
  induction k with
  | zero => exact lbi_zero _
  | succ k ih =>
    rw [← oadd_mulNat hB hBp k, ← oadd_mulNat hB hBp (k + 1)]
    refine lbi_oadd_prin hB (wnf_mulNat hB hBp k) (wnf_mulNat hB hBp (k + 1))
      (Or.inr (mulNat_lt_succ hBp k)) ih (Or.inr ?_)
    exact (wnf_mulNat hB hBp (k + 2) : WNF (Tm.plus B (mulNat B (k + 1))))

/-- 列 `t[n] = B·(n+2)` の `BInv` -/
theorem binv_mul {t B : Tm} (hB : WNF B) (hBp : isPrincipal B = true) (hd : dom t = .omega)
    (hf : ∀ n, fundNat t n = mulNat B (n + 2)) : BInv t := by
  refine ⟨fun _ n => ?_, fun σ h => by rw [hd] at h; cases h⟩
  rw [hf, hf, show n + 1 + 2 = n + 2 + 1 by omega]
  exact lbi_mulNat hB hBp (n + 2)

/-- `Ψ_{Ω_c}(0)` -/
theorem binv_psi_zero {c : Tm} (h : WNF (.Psi (.Om c) .zero)) : BInv (.Psi (.Om c) .zero) := by
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
    have hcF := h.psi.piF.om.1
    exact binv_mul (wnf_omOf (predT_WNF hcF hs)) (omOf_principal _) hdom hf
  · cases e

/-- `Ψ_{Ω_d}(X'+1)` -/
theorem binv_psi_succ_om {d X : Tm} (h : WNF (.Psi (.Om d) X)) (hs : isSucc X = true) :
    BInv (.Psi (.Om d) X) := by
  have hXF := h.psi.aF
  have hcs := cs_succ_om (d := d) hXF hs
  have hdom : dom (.Psi (.Om d) X) = .omega := by rw [dom_psi, hcs]; rfl
  have hf : ∀ n, fundNat (.Psi (.Om d) X) n = mulNat (.Psi (.Om d) (predT X)) (n + 2) := by
    intro n; rw [fundNat_psi, hcs]; rfl
  exact binv_mul (psi_pred_WNF h hs) rfl hdom hf

/-! ### 崩壊の場合分け -/

/-- 崩壊の残りの場合（`X ≠ 0`、後者なら崩壊先は `Ξ`） -/
def PsiRestBInv : Prop :=
  ∀ π X, WNF (.Psi π X) → X ≠ .zero → (isSucc X = true → ∃ n p, π = .Xi n p) →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) → BInv (.Psi π X)

theorem psiBInv_of (hR : PsiRestBInv) : PsiBInv := by
  intro π X ht ih
  by_cases hX0 : X = .zero
  · subst hX0
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact binv_psi_zero ht
    · exact binv_psi_zero ht
    · exact absurd (ht.psi.act n p rfl) (not_lt_zero p)
  · by_cases hs : isSucc X = true
    · rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
      · exact binv_psi_succ_om ht hs
      · exact binv_psi_succ_om ht hs
      · exact hR _ _ ht hX0 (fun _ => ⟨n, p, rfl⟩) ih
    · exact hR _ _ ht hX0 (fun hs' => absurd hs' hs) ih

end MahloOCF.FS
