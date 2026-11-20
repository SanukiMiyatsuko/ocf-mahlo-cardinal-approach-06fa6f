import Mahlo.FS.BachXi

/-! 族の閉包（`mahloVK`）の梯子の道具。

区間 `(Ξ_m(A), Ξ_m(A')]` に現れる `E ∈ (A, A']` の評価 `Ξ_m(A) ≤ base(Ξ_m(E))[0]` は、

* `E` の `M_m` についての前線に `Ξ_m(A)` 以上の元があれば、底の閉包はその上から始まる（`front_lt_base_f0`）。
* そうでなければ、`E[0] = A`（`Ξ_m(E[0]) ≤ base(Ξ_m(E))[0]`）か、`E[0]` も同じ条件を満たす（帰納法）。

引数の段で `LBI A A'` が成り立たない種つきの近似（`Ξ_m(pre ⊕ (P' # x))`）では、`Ξ_m(A) < Ξ_m(E)` の `E` だけを
見ればよい（`BachSeed.lean` の `xi_le_base_f0_relF`）。 -/

namespace MahloOCF.FS

open Tm

/-- 前線の元が `Ξ_m(A)` 以上なら `Ξ_m(A) ≤ base(Ξ_m(E))[0]` -/
theorem xi_le_base_f0_of_front {m : Nat} {A E f : Tm} (hA : WNF (.Xi m A)) (hE : WNF (.Xi m E))
    (hf : f ∈ fr (.M m) E) (hAf : Le (.Xi m A) f) : Le (.Xi m A) (fund (base (.Xi m E)) .zero) := by
  have hf' : f ∈ fr (.Xi m E) (.Xi m E) := (fr_rho_iff hE).mpr hf
  have hfF := (fr_elem hE.xi.2.1 hf).1
  have hbF : WNF (base (.Xi m E)) := wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))
  exact Or.inr (lt_of_le_of_ltY hA hfF (wnf_f0 hbF) hAf (front_lt_base_f0 hE hf'))

/-- 前線の元が全て `y` 未満か、`y` 以上の元があるか -/
theorem fr_all_or_exists (R x y : Tm) :
    (∀ f, f ∈ fr R x → Lt f y) ∨ ∃ f, f ∈ fr R x ∧ ¬ Lt f y := by
  cases h : (fr R x).any (fun f => !ltB f y) with
  | true =>
    obtain ⟨f, hf, hfy⟩ := List.any_eq_true.mp h
    refine Or.inr ⟨f, hf, fun hlt => ?_⟩
    rw [ltB_iff.mpr hlt] at hfy
    cases hfy
  | false =>
    refine Or.inl (fun f hf => ?_)
    cases e : ltB f y with
    | true => exact ltB_iff.mp e
    | false =>
      have : (fr R x).any (fun f => !ltB f y) = true :=
        List.any_eq_true.mpr ⟨f, hf, by rw [e]; rfl⟩
      rw [h] at this
      cases this

/-! ### 前線による比較と種の閉性 -/

/-- 種 `P'` は `B` 未満の引数について閉じている：前線が全て `P'` 未満の `D < B` なら `Ξ_m(D) < P'` -/
def XiClosed (m : Nat) (P' B : Tm) : Prop :=
  ∀ D, WNF (.Xi m D) → Lt D B → (∀ f, f ∈ fr (.M m) D → Lt f P') → Lt (.Xi m D) P'

/-- `Ξ_m(W)` は `W` 未満の引数について閉じている -/
theorem xiClosed_xi {m : Nat} {W : Tm} (hW : WNF (.Xi m W)) : XiClosed m (.Xi m W) W :=
  fun _ hD hDW hfr => xi_step hD hW hDW hfr

/-- `Ψ_{Ξ_m(q)}(X)`（`q < X`）は `q` 未満の引数について閉じている -/
theorem xiClosed_psi {m : Nat} {q X : Tm} (hp : WNF (.Psi (.Xi m q) X)) (hqX : Lt q X) :
    XiClosed m (.Psi (.Xi m q) X) q := by
  intro D hD hDq hfr
  have hρ := hp.psi.piF
  have hXF := hp.psi.aF
  have hqF := hρ.xi.2.1
  have hDF := hD.xi.2.1
  have hpρ : Lt (.Psi (.Xi m q) X) (.Xi m q) := lt_psi_targetY hp
  have hDX : Lt D X := lt_transY hDF hqF hXF hDq hqX
  have hDC : inC D X (.Psi (.Xi m q) X) = true :=
    inC_of_fr D hD.xi.2.2.2 (fun v hv h => lt_transY (hDF.of_mem_subs hv) hDF hXF h hDX)
      (fun f hf => inC_of_lt_node (fr_node hf) (hfr f hf))
  have hyC : inC (.Xi m D) X (.Psi (.Xi m q) X) = true := inC_xi_iff.mpr (Or.inr ⟨hDC, hDX⟩)
  have hyρ : Lt (.Xi m D) (.Xi m q) :=
    xi_step hD hρ hDq (fun f hf => lt_transY (fr_elem hDF hf).1 hp hρ (hfr f hf) hpρ)
  exact coll_psiY hp hD hyC hyρ

end MahloOCF.FS
