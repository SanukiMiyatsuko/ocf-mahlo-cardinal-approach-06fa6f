import Mahlo.FS.BachPlain

/-! 目標そのものへの対角化（`R` の共終数が `π`）の `BInv`：列は塔 `t[n] = γ_{n+1}`、`γ_0 = 0`、
`γ_{k+1} = Ψ_π(pre ⊕ (c ⊕ R[γ_k]))` そのものなので、`LBI (t[n]) (t[n+1])` は `R` の区間の下界の移送と、一つ前の
`LBI (t[n-1]) (t[n])` から出る（`n` についての帰納法）。 -/

namespace MahloOCF.FS

open Tm

/-- 近似の崩壊は崩壊先の底より大きい（添字が後者でないとき） -/
theorem base_lt_psi_apx {π X R c ξ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hRi : BigInv R π)
    (hadj : AdjOK π pre R (fundBig R .zero) c) (hξ : WNF ξ) (hξπ : Lt ξ π) (hξns : ¬ isSucc ξ = true) :
    Lt (base π) (.Psi π (apx pre c (fundBig R ξ))) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hπM := hT.notM
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hRP := hRi.props
  have hxF := hRP.nf ξ hξ hξπ
  have hx0 := fundBig_ne_zero hRi hπM hξ hξπ
  have hA'F := wnf_oadd hadj.cF hxF
  have hAF := wnf_oadd hPF hA'F
  have hA'0 : oadd c (fundBig R ξ) ≠ .zero := fun e => hx0 (oadd_eq_zero hadj.cF hxF e).2
  have hA0 : apx pre c (fundBig R ξ) ≠ .zero := fun e => hA'0 (oadd_eq_zero hPF hA'F e).2
  rcases hT with rfl | ⟨c', rfl, hs⟩ | ⟨m, d, rfl⟩
  · exact lt_psi_psi_same.mpr (zero_lt hA0)
  · exact lt_psi_psi_same.mpr (zero_lt hA0)
  · show Lt (.Psi (.Xi m d) (sc d)) _
    refine lt_psi_psi_same.mpr (succT_lt_of_not_succ hπ.xi.2.1 hAF ?_ ?_)
    · rw [isSucc_oadd hPF hA'F hA'0, isSucc_oadd hadj.cF hxF hx0]
      exact hRi.nsucc ξ hξ hξπ hξns (Or.inr (by intro e; cases e))
    · exact validR_iff.mp (hadj.valid _ hxF (fundBig_zero_le hRP hξ hξπ)) d rfl

/-- 目標そのものへの対角化 -/
theorem binv_psi_diag_in {π X R : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big π) (hRb : BInv R) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hπM := hT.notM
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hRi := (inv_of R hR.1).2 π hRd
  have hRP := hRi.props
  have hr : (info R).seq.dom = .big π := hRd
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns (fundBig R .zero)
  have hcS := mkApp_shape hπ hmk
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ hd => by
      rw [hr] at hd; cases hd; exact Or.inr (Or.inl (outsideMode_self hπM _ _)))
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, ltB_self, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam π π (.psi π) pre R (info R).seq c .zero := ⟨_, rfl⟩
  have hγ0 : γ 0 = .zero := by rw [hγdef]; exact gam_in_zero hπM _ _ _ _
  have hγS : ∀ n, γ (n + 1) = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [hγdef]; exact gam_in_succ hπM _ _ _ _ n
  have hfN : ∀ n, fundNat (.Psi π X) n = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [fundNat_psi, hcs, hγdef]; exact nat_app_in hπM _ _ _ _ hr n
  have htN := (props_all _ ht).1 hdom
  -- 塔は列そのもの
  have hγt : ∀ n, γ (n + 1) = fundNat (.Psi π X) n := fun n => by rw [hγS, hfN]
  have hγF : ∀ n, WNF (γ n) := by
    intro n; cases n with
    | zero => rw [hγ0]; exact WNF.zero
    | succ n => rw [hγt]; exact htN.nf n
  have hγπ : ∀ n, Lt (γ n) π := by
    intro n; cases n with
    | zero => rw [hγ0]; exact zero_lt hT.ne_zero
    | succ n => rw [hγt]; exact lt_transY (htN.nf n) ht hπ (htN.lt n) (lt_psi_targetY ht)
  have hxF : ∀ n, WNF (fundBig R (γ n)) := fun n => hRP.nf _ (hγF n) (hγπ n)
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN, combine_psi_zero pre hadj.cF (hxF n)]
  have hγm : ∀ n, Lt (γ n) (γ (n + 1)) := by
    intro n; cases n with
    | zero => rw [hγ0, hγt, hf]; exact zero_lt (fun e => by cases e)
    | succ n => rw [hγt, hγt]; exact htN.mono n
  -- 添字は `0` か底より大きい主要項
  have hγns : ∀ n, ¬ isSucc (γ n) = true := by
    intro n; cases n with
    | zero => rw [hγ0]; simp [isSucc, summands]
    | succ n =>
      rw [hγt, hf]
      intro he
      simp [isSucc, summands, one] at he
      have hx0 := fundBig_ne_zero hRi hπM (hγF n) (hγπ n)
      have hPF := wnf_ofSummands (nfl_append_left hXn)
      have hA'F := wnf_oadd hadj.cF (hxF n)
      exact hx0 (oadd_eq_zero hadj.cF (hxF n) (oadd_eq_zero hPF hA'F he.2).2).2
  refine ⟨fun _ n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  induction n with
  | zero =>
    have hA := htN.nf 0
    have hA' := htN.nf 1
    rw [hf] at hA hA' ⊢
    rw [hf]
    refine lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF 0) (hxF 1)
      (Or.inr (hRP.mono _ _ (hγF 0) (hγF 1) (hγm 0) (hγπ 1))) (hRP.lt _ (hγF 1) (hγπ 1)) ?_ hA hA'
    refine hRb.big π hRd (γ 0) (γ 1) (hγF 0) (hγF 1) (Or.inr (hγm 0)) (hγπ 1) (Or.inl hγ0) ?_
    rw [hγ0]; exact lbi_zero _
  | succ n ih =>
    have hA := htN.nf (n + 1)
    have hA' := htN.nf (n + 2)
    rw [hf] at hA hA' ⊢
    rw [hf]
    refine lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF (n + 1)) (hxF (n + 2))
      (Or.inr (hRP.mono _ _ (hγF _) (hγF _) (hγm (n + 1)) (hγπ _))) (hRP.lt _ (hγF _) (hγπ _)) ?_ hA hA'
    have hadm : γ (n + 1) = .zero ∨ (isPrincipal (γ (n + 1)) = true ∧ Lt (base π) (γ (n + 1))) := by
      right
      rw [hγt, hf]
      exact ⟨rfl, base_lt_psi_apx ht hsX hRi hadj (hγF n) (hγπ n) (hγns n)⟩
    refine hRb.big π hRd (γ (n + 1)) (γ (n + 2)) (hγF _) (hγF _) (Or.inr (hγm _)) (hγπ _) hadm ?_
    rw [hγt, hγt]; exact ih

end MahloOCF.FS
