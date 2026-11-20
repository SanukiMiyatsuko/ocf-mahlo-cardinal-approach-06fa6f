import Mahlo.FS.BachArg

/-! 崩壊の持ち上げ（`lbi_psi_apx`）と、素の近似の場合の `BInv`：極限 `X = pre + R` で `R` の列が `ω` 型
（`binv_psi_lim_nat`）か、共終数 `σ < π` の正則項型（`binv_psi_lim_big`）。近似 `Ψ_π(pre ⊕ (c ⊕ R[ν]))` の区間の下界は
`R` の区間の下界から出る（調整 `c` は `0` か `rt + 1`、`psi_harg_apx`）。 -/

namespace MahloOCF.FS

open Tm

/-- 崩壊の持ち上げ：近似の引数 `R` の区間の下界から近似の区間の下界 -/
theorem lbi_psi_apx {π X R c x y : Tm} {pre : List Tm}
    (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R]) (hcF : WNF c) (hcR : Lt c R)
    (hcS : AdjShape π pre c) (hx : WNF x) (hy : WNF y) (hxy : Le x y) (hyR : Lt y R) (hL : LBI x y)
    (hA : WNF (.Psi π (apx pre c x))) (hA' : WNF (.Psi π (apx pre c y))) :
    LBI (.Psi π (apx pre c x)) (.Psi π (apx pre c y)) :=
  lbi_psi hA hA' (fun _ hB h1 h2 => psi_harg_apx ht hsX hcF hcR hcS hx hy hxy hyR hL hA hB h1 h2)

/-- `mkApp` の調整の形 -/
theorem mkApp_shape {π : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {c : Tm} (hπ : WNF π)
    (h : mkApp π (.psi π) pre R r .zero .zero = some (.app π (.psi π) pre R r .zero c)) :
    AdjShape π pre c := by
  obtain ⟨c', he, -, hS⟩ := mkApp_psi_wnf hπ h
  simp only [SeqD.app.injEq, true_and] at he
  rw [he]; exact hS

/-- 極限 `X = pre + R` で `R` の列が `ω` 型 -/
theorem binv_psi_lim_nat {π X R : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .omega) (hRb : BInv R) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hRP := (props_all R hR.1).1 hRd
  have hr : (info R).seq.dom = .omega := hRd
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  have hcS := mkApp_shape hP.piF hmk
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ hd => by rw [hr] at hd; cases hd)
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]
    simp only [SeqD.dom, hr]
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundNat R n)) := by
    intro n
    rw [fundNat_psi, hcs]
    simp only [SeqD.nat, hr]
    exact congrArg (Tm.Psi π) (combine_psi_zero pre hadj.cF (hRP.nf n))
  have htP := (props_all _ ht).1 hdom
  refine ⟨fun _ n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  have hA := htP.nf n
  have hA' := htP.nf (n + 1)
  rw [hf] at hA hA' ⊢
  rw [hf]
  exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hRP.nf n) (hRP.nf (n + 1)) (Or.inr (hRP.mono n))
    (hRP.lt (n + 1)) (hRb.om hRd n) hA hA'

/-- 極限 `X = pre + R` で `R` の共終数 `σ` が `π` 未満 -/
theorem binv_psi_lim_big {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big σ) (hσπ : Lt σ π) (hRb : BInv R) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hRP := (props_all R hR.1).2 σ hRd
  have hr : (info R).seq.dom = .big σ := hRd
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  have hcS := mkApp_shape hP.piF hmk
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ' hd => by rw [hr] at hd; cases hd; exact Or.inl (ltB_iff.mpr hσπ))
  have hdom : dom (.Psi π X) = .big σ := by
    rw [dom_psi, hcs]
    simp only [SeqD.dom, hr, ltB_iff.mpr hσπ, ↓reduceIte]
  have hf : ∀ ξ, WNF ξ → Lt ξ σ →
      fundBig (.Psi π X) ξ = .Psi π (apx pre c (fundBig R ξ)) := by
    intro ξ hξ hξσ
    rw [fundBig_psi, hcs]
    exact congrArg (Tm.Psi π) (combine_psi_zero pre hadj.cF (hRP.nf ξ hξ hξσ))
  have htB := (props_all _ ht).2 σ hdom
  refine ⟨(fun hd' => by rw [hdom] at hd'; cases hd'), fun σ' hd ξ η hξ hη hξη hησ hadm hL => ?_⟩
  rw [hdom] at hd
  cases hd
  have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hRP.σF hξη hησ
  have hA := htB.nf ξ hξ hξσ
  have hA' := htB.nf η hη hησ
  rw [hf ξ hξ hξσ] at hA ⊢
  rw [hf η hη hησ] at hA' ⊢
  exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hRP.nf ξ hξ hξσ) (hRP.nf η hη hησ)
    (bigProps_mono_le hRP hξ hη hξη hησ) (hRP.lt η hη hησ)
    (hRb.big σ hRd ξ η hξ hη hξη hησ hadm hL) hA hA'

/-! ### 崩壊の残りの場合分け -/

/-- 対角化（`R` の共終数 `σ` が `π` 以上） -/
def PsiDiagBInv : Prop :=
  ∀ π X R σ pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big σ → BInv R → ¬ Lt σ π →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) → BInv (.Psi π X)

/-- `Ξ_n(p)` への崩壊で `X` が後者 -/
def PsiXiSuccBInv : Prop :=
  ∀ n p X, WNF (.Psi (.Xi n p) X) → isSucc X = true →
    (∀ u, u.size < (Tm.Psi (.Xi n p) X).size → WNF u → BInv u) → BInv (.Psi (.Xi n p) X)

theorem psiRestBInv_of (hD : PsiDiagBInv) (hS : PsiXiSuccBInv) : PsiRestBInv := by
  intro π X ht hX0 hsx ih
  by_cases hs : isSucc X = true
  · obtain ⟨n, p, rfl⟩ := hsx hs
    exact hS n p X ht hs ih
  · have hX := ht.psi.aF
    have hne := summands_ne_nil hX0
    obtain ⟨pre, R, hsX⟩ : ∃ pre R, summands X = pre ++ [R] :=
      ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
    have hRX : R ∈ summands X := by rw [hsX]; simp
    have hR := summands_WNF X hX R hRX
    have hRsz : R.size < (Tm.Psi π X).size := by
      have := size_le_of_mem_subs (mem_subs_of_mem_summands hRX)
      simp only [Tm.size]; omega
    have hRb := ih R hRsz hR.1
    cases hd : dom R with
    | zero =>
      have := (dom_eq_zero_iff hR.1).mp hd
      rw [this] at hR
      cases hR.2
    | one =>
      exact absurd (by rw [isSucc_of_last hsX hR.2]; exact (dom_eq_one_iff hR.1).mp hd) hs
    | omega => exact binv_psi_lim_nat ht hsX hs hd hRb
    | big σ =>
      by_cases hσπ : Lt σ π
      · exact binv_psi_lim_big ht hsX hs hd hσπ hRb
      · exact hD π X R σ pre ht hsX hs hd hRb hσπ ih

/-- 対角化と後者の場合から Bachmann 性 -/
theorem bachHyp_of_rest (hD : PsiDiagBInv) (hS : PsiXiSuccBInv) : BachHyp :=
  bachHyp_of_binv (psiBInv_of (psiRestBInv_of hD hS))

end MahloOCF.FS
