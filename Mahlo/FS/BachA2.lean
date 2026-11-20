import Mahlo.FS.BachDiagM

/-! 外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` でない場合（族の閉包を添字にする場合、`A2`）の `BInv`。

`t = Ψ_π(X)`、`X = pre + R`、`R` の共終数 `σ = Ξ_k(e)`。列は `t[ν] = Ψ_π(pre ⊕ (c ⊕ R[y_ν]))` で、添字 `y` は
種 `p = a2Seed σ π` の上の `σ` の族の閉包 `mahloVK k e _ σ (some p)`。

* 種 `p` は `Ψ_σ(β)`（`e < β`）の形（`σ` の族について閉じた点）なので、添字の列の梯子は種つきの近似の枠組み
  （`seqLad_mahloVK`・`seedPack_psi`・`seedHull_psi`）で得られる（`seqLad_a2`）。
* 添字は全て `σ` の始点より大きい主要項なので、`R` の区間の下界の移送（`BInv R`）と `π` への崩壊の持ち上げ
  （`lbi_psi_apx`）で `t` の梯子を得る（`binv_a2`）。 -/

namespace MahloOCF.FS

open Tm

/-- 族の閉包の添字の梯子 -/
theorem seqLad_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    (ih : ∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) :
    SeqLad (mahloVK k e (info e).sums (.Xi k e) (some p)) := by
  have heF := H.hσ.xi.2.1
  obtain ⟨β, hpβ, hβF⟩ := H.hpform
  -- 大きさの評価：`σ` は `R` の部分項
  have hRX : R ∈ summands X := by rw [H.hsX]; simp
  have hsz : (Tm.Xi k e).size < (Tm.Psi π X).size := by
    have h2 := size_le_of_mem_subs H.hRi.σsub
    have h3 := size_le_of_mem_subs (mem_subs_of_mem_summands hRX)
    simp only [Tm.size] at h2 h3 ⊢
    omega
  refine seqLad_mahloVK_psi hβF (hβF.psi.act k e rfl) (by rw [hpβ])
    (fun R' hR' => ih R' ?_ (summands_WNF e heF R' hR').1)
    (fun hqS => ih (succM k) ?_ (by rw [← hqS]; exact heF)) (fun hd n => ?_) (fun τ hd => ?_)
  · have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands hR')
    simp only [Tm.size] at h1 hsz ⊢
    omega
  · rw [← hqS]; simp only [Tm.size] at hsz ⊢; omega
  · have F := famNat_a2 H hd
    exact ⟨F.F n, F.mono n⟩
  · have F := famBig_a2 H hd
    exact ⟨F.pos, F.F, fun ξ η hξ hη hξη hητ => F.mono ξ η hξ hη hξη hητ⟩

/-- 族の閉包を添字にする外に足す型の対角化の `BInv` -/
theorem binv_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    (hRb : BInv R) (ih : ∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) : BInv (.Psi π X) := by
  have ht := H.ht
  have hP := ht.psi
  have hπ := hP.piF
  have hsX := H.hsX
  have hRi := H.hRi
  have hRP := hRi.props
  have hRd := H.hRd
  have hadj := H.hadj
  have hcS := mkApp_shape hπ H.hmk
  have hBF := H.hBF
  have hpF := H.hpF
  have L := seqLad_a2 H ih
  have hdt : dom (.Psi π X) = (SeqD.iapp (.psi π) pre (info R).seq .zero c
      (mahloVK k e (info e).sums (.Xi k e) (some p))).dom := by rw [dom_psi, H.hcs]
  obtain ⟨hne0, hne1⟩ := mahloVK_dom_ne k e (info e).sums (.Xi k e) (some p)
  refine ⟨fun hd n => ?_, fun τ hd ξ η hξ hη hξη hητ hadm hL => ?_⟩
  · -- `ω` 型
    have hd0 := hd
    rw [hdt] at hd
    have hs : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom = .omega := by
      cases hs : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom with
      | omega => rfl
      | big τ' => simp [SeqD.dom, hs] at hd
      | zero => exact absurd hs hne0
      | one => exact absurd hs hne1
    obtain ⟨y, hydef⟩ : ∃ y : Nat → Tm,
        y = fun n => (mahloVK k e (info e).sums (.Xi k e) (some p)).nat n := ⟨_, rfl⟩
    have hyn : ∀ n, (mahloVK k e (info e).sums (.Xi k e) (some p)).nat n = y n := fun n => by
      rw [hydef]
    have F := famNat_a2 H hs
    rw [← hydef] at F
    have hyF : ∀ n, WNF (y n) := F.F
    have hyσ : ∀ n, Lt (y n) (.Xi k e) := F.ltρ
    have hyB : ∀ n, Lt (base (.Xi k e)) (y n) := fun n =>
      lt_of_le_of_ltY hBF hpF (hyF n) H.hBp
        (lt_of_lt_of_leY hpF (hyF 0) (hyF n) (F.seed p rfl) (F.mono_le (Nat.zero_le n)))
    have hxF : ∀ n, WNF (fundBig R (y n)) := fun n => hRP.nf _ (hyF n) (hyσ n)
    have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (y n))) := by
      intro n
      rw [fundNat_psi, H.hcs]
      show Tm.Psi π (combine (.psi π) pre c .zero (fundBig R
        ((mahloVK k e (info e).sums (.Xi k e) (some p)).nat n))) = _
      rw [hyn n, combine_psi_zero pre hadj.cF (hxF n)]
    have hLy : LBI (y n) (y (n + 1)) := by
      have h := L.1 hs n
      rw [hyn, hyn] at h
      exact h
    have hLR : LBI (fundBig R (y n)) (fundBig R (y (n + 1))) :=
      hRb.big (.Xi k e) hRd (y n) (y (n + 1)) (hyF n) (hyF _) (Or.inr (F.mono n)) (hyσ _)
        (Or.inr ⟨F.prin n, hyB n⟩) hLy
    have htN := (props_all _ ht).1 hd0
    have hA := htN.nf n
    have hA' := htN.nf (n + 1)
    rw [hf] at hA hA' ⊢
    rw [hf]
    exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF n) (hxF (n + 1))
      (Or.inr (hRP.mono _ _ (hyF n) (hyF _) (F.mono n) (hyσ _))) (hRP.lt _ (hyF _) (hyσ _)) hLR hA hA'
  · -- 正則項型
    have hd0 := hd
    rw [hdt] at hd
    cases hs : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom with
    | omega => simp [SeqD.dom, hs] at hd
    | zero => exact absurd hs hne0
    | one => exact absurd hs hne1
    | big τ' =>
      simp only [SeqD.dom, hs, Cof.big.injEq] at hd
      subst hd
      obtain ⟨y, hydef⟩ : ∃ y : Tm → Tm,
          y = fun ξ => (mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ := ⟨_, rfl⟩
      have hyξ : ∀ ξ, (mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ = y ξ := fun ξ => by
        rw [hydef]
      have F := famBig_a2 H hs
      rw [← hydef] at F
      have hτF := F.σF
      have hξτ : Lt ξ τ' := lt_of_le_of_ltY hξ hη hτF hξη hητ
      have hyF : ∀ ζ, WNF ζ → Lt ζ τ' → WNF (y ζ) := F.F
      have hyσ : ∀ ζ, WNF ζ → Lt ζ τ' → Lt (y ζ) (.Xi k e) := F.ltρ
      have hyB : Lt (base (.Xi k e)) (y ξ) :=
        lt_of_le_of_ltY hBF hpF (hyF ξ hξ hξτ) H.hBp
          (lt_of_lt_of_leY hpF (hyF .zero WNF.zero F.pos) (hyF ξ hξ hξτ) (F.seed p rfl) (F.le0 hξ hξτ))
      have hyle : Le (y ξ) (y η) := by
        rcases hξη with e' | h
        · rw [e']; exact Or.inl rfl
        · exact Or.inr (F.mono ξ η hξ hη h hητ)
      have hxF : ∀ ζ, WNF ζ → Lt ζ τ' → WNF (fundBig R (y ζ)) := fun ζ hζ hζτ =>
        hRP.nf _ (hyF ζ hζ hζτ) (hyσ ζ hζ hζτ)
      have hf : ∀ ζ, WNF ζ → Lt ζ τ' →
          fundBig (.Psi π X) ζ = .Psi π (apx pre c (fundBig R (y ζ))) := by
        intro ζ hζ hζτ
        rw [fundBig_psi, H.hcs]
        show Tm.Psi π (combine (.psi π) pre c .zero (fundBig R
          ((mahloVK k e (info e).sums (.Xi k e) (some p)).big ζ))) = _
        rw [hyξ ζ, combine_psi_zero pre hadj.cF (hxF ζ hζ hζτ)]
      have hLy : LBI (y ξ) (y η) := by
        have h := L.2 τ' hs ξ η hξ hη hξη hητ hadm hL
        rw [hyξ, hyξ] at h
        exact h
      have hLR : LBI (fundBig R (y ξ)) (fundBig R (y η)) :=
        hRb.big (.Xi k e) hRd (y ξ) (y η) (hyF ξ hξ hξτ) (hyF η hη hητ) hyle (hyσ η hη hητ)
          (Or.inr ⟨F.prin ξ, hyB⟩) hLy
      have htB := (props_all _ ht).2 τ' hd0
      have hA := htB.nf ξ hξ hξτ
      have hA' := htB.nf η hη hητ
      rw [hf ξ hξ hξτ] at hA ⊢
      rw [hf η hη hητ] at hA' ⊢
      exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF ξ hξ hξτ) (hxF η hη hητ)
        (bigProps_mono_le hRP (hyF ξ hξ hξτ) (hyF η hη hητ) hyle (hyσ η hη hητ))
        (hRP.lt _ (hyF η hη hητ) (hyσ η hη hητ)) hLR hA hA'

/-- 外に足す型の対角化で `Ψ_π(X) < Ψ_σ(X)` でない場合の `BInv` -/
theorem psiDiagFamBInv : PsiDiagFamBInv := by
  intro π X R σ pre ht hsX hns hRd hRb hπσ hσM hT ih
  have hX := ht.psi.aF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hRi := (inv_of R hR.1).2 σ hRd
  obtain ⟨k, e, p, c, rfl, H⟩ := a2_mk ht hsX hns hRd hRi hπσ hσM hT (fun u _ hu => inv_of u hu)
  exact binv_a2 H hRb ih

end MahloOCF.FS

/-! `#print axioms` の出力を固定する検査。 -/

/-- info: 'MahloOCF.FS.psiDiagFamBInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.psiDiagFamBInv
