import Mahlo.FS.FamSeq

/-! 族の閉包 `mahloVK` の各分岐の `ω` 型の列（`FamNat`）。

* `R` の列が `ω` 型：`y_n = Ξ_m(pre ⊕ (P' # R[n]))`（`famNat_app_nat`）。
* `R` の共終数が `M_m`：塔 `γ_0 = P'`、`γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`、`y_n = γ_{n+1}`（`famNat_app_M`）。
* `Ω` の塔 `y_n = Ω_{⋯Ω_{s+1}⋯+1}`（`famNat_tower`）。 -/

namespace MahloOCF.FS

open Tm

theorem XG.hq0 {m : Nat} {q P' R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R) : q ≠ .zero := by
  intro h; have := G.hRq; rw [h] at this; simp [summands] at this

theorem XG.xa0 {m : Nat} {q P' R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R) {x : Tm}
    (hx : WNF x) (hx0 : x ≠ .zero) : xa pre P' x ≠ .zero := by
  intro e
  have h1 := G.hxA hx
  rw [e] at h1
  rcases h1 with e' | h1
  · exact hx0 e'
  · exact not_lt_zero _ h1

/-! ### `R` の列が `ω` 型 -/

theorem app_xi_dom_nat {τ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega) :
    (SeqD.app τ (.xi m) pre R r P' .zero).dom = .omega := by
  simp only [SeqD.dom, hr]

theorem app_xi_nat {τ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega)
    (hP' : WNF P') {n : Nat} (hx : WNF (r.nat n)) :
    (SeqD.app τ (.xi m) pre R r P' .zero).nat n = .Xi m (xa pre P' (r.nat n)) := by
  simp only [SeqD.nat, hr, Gen.ap]
  rw [combine_xi m pre hP' hx]

/-- `R` の列が `ω` 型の近似 `Ξ_m(pre ⊕ (P' # R[n]))` の族の列 -/
theorem famNat_app_nat {m : Nat} {q P' R τ : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (hRd : dom R = .omega) (hRi : NatInv R)
    (hPρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) →
        Le (.Xi m c) P' ∨ Lt (.Xi m c) (.Xi m (xa pre P' (fundNat R 0))))
    (hseed : ∀ p, P = some p → (WNF p ∧ Le p P') ∨ Lt p (.Xi m (xa pre P' (fundNat R 0)))) :
    FamNat m q P (fun n => (SeqD.app τ (.xi m) pre R (info R).seq P' .zero).nat n) := by
  have hr : (info R).seq.dom = .omega := hRd
  have hRP := hRi.props
  have hfun : (fun n => (SeqD.app τ (.xi m) pre R (info R).seq P' .zero).nat n) =
      (fun n => .Xi m (xa pre P' (fundNat R n))) :=
    funext fun n => app_xi_nat hr G.hPF (hRP.nf n)
  rw [hfun]
  have hqF := G.hqF
  have hRCρ : inC R q (.Xi m q) = true := G.pre_inCρ R (by simp)
  have hxCM : ∀ n, inC (fundNat R n) (xa pre P' (fundNat R n)) (.M m) = true := fun n => by
    have hRC := G.pre_inC (hRP.nf n) (hRi.gap n) (fun h0 => absurd h0 (hRi.pos n)) G.hqC R (by simp)
    exact hRi.ub _ _ n (G.hAF (hRP.nf n)) (G.xa0 (hRP.nf n) (hRi.pos n)) (Cut.of_wnf G.hMF) hRC
  have hy0F : WNF (.Xi m (xa pre P' (fundNat R 0))) :=
    G.nf (hRP.nf 0) (hRP.lt 0) (hRi.gap 0) (fun h0 => absurd h0 (hRi.pos 0)) (hxCM 0)
  have hP'y := G.seed_lt (hRP.nf 0) (hRP.lt 0) hy0F
  refine famNat_xa G (fun n => fundNat R n) hRP.nf hRP.lt hRi.gap
    (fun n h0 => absurd h0 (hRi.pos n)) hRP.mono hxCM
    (fun n => hRi.ub q _ n hqF G.hq0 (Cut.of_wnf G.ht) hRCρ) hPρ
    (fun g d n hg hg0 hd hρC hρd hPC => ?_) (fun g d n hg hg0 hd => hRi.ub2 g d n hg hg0 hd)
    (fun c' N _ hc' hc'R _ _ _ _ => ?_)
    (fun c h1 h2 h3 h4 => (hrest c h1 h2 h3 h4).elim
      (fun h => lt_of_le_of_ltY h1 G.hPF hy0F h hP'y) id)
    (fun p hp => (hseed p hp).elim (fun h => lt_of_le_of_ltY h.1 G.hPF hy0F h.2 hP'y) id)
  · rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, -⟩
    · exact absurd h1 hρd
    exact ⟨hRi.ub g d n hg hg0 hd (inC_of_mem_summands hqF hqC G.hRq), hP'ub g d hg hg0 hd hρC hρd hPC⟩
  · obtain ⟨n, hn⟩ := hRP.cof c' hc' hc'R
    exact ⟨n + 1, lt_of_le_of_ltY hc' (hRP.nf n) (hRP.nf _) hn (hRP.mono n)⟩

/-! ### `R` の共終数が `M_m`（値の塔） -/

theorem gam_xi_M_zero {τ R P' : Tm} {m k : Nat} {pre : List Tm} {r : SeqD} :
    gam τ (.M k) (.xi m) pre R r .zero P' 0 = P' := by
  simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte]

theorem gam_xi_M_succ {τ R P' : Tm} {m k : Nat} {pre : List Tm} {r : SeqD} (n : Nat) :
    gam τ (.M k) (.xi m) pre R r .zero P' (n + 1) =
      .Xi m (combine (.xi m) pre .zero .zero (r.big (gam τ (.M k) (.xi m) pre R r .zero P' n))) := by
  simp only [gam, canonK, outsideMode, argOf, seedOut, Bool.false_eq_true, Bool.false_and,
    ↓reduceIte, Gen.ap]

theorem app_xi_M_nat {τ R P' : Tm} {m k : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .big (.M k))
    (hτ : ltB (.M k) τ = false) (n : Nat) :
    (SeqD.app τ (.xi m) pre R r P' .zero).nat n = gam τ (.M k) (.xi m) pre R r .zero P' (n + 1) := by
  rw [gam_xi_M_succ]
  simp only [SeqD.nat, hr, hτ, Bool.false_eq_true, ↓reduceIte, argOf, canonK, outsideMode, seedOut,
    Bool.false_and, Gen.ap]

theorem app_xi_M_dom {τ R P' : Tm} {m k : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .big (.M k))
    (hτ : ltB (.M k) τ = false) : (SeqD.app τ (.xi m) pre R r P' .zero).dom = .omega := by
  simp only [SeqD.dom, hr, hτ, Bool.false_eq_true, ↓reduceIte]

/-- `R` の共終数が `M_m` の値の塔 `γ_0 = P'`、`γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])` の族の列 -/
theorem famNat_app_M {m : Nat} {q P' R τ : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q .zero pre rest R) (hRd : dom R = .big (.M m)) (hRi : BigInv R (.M m))
    (hτ : ltB (.M m) τ = false) (hP'F : WNF P') (hP'ρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) →
        Le (.Xi m c) P' ∨ Lt (.Xi m c) (.Xi m (xa pre .zero (fundBig R P'))))
    (hseed : ∀ p, P = some p → (WNF p ∧ Le p P') ∨ Lt p (.Xi m (xa pre .zero (fundBig R P')))) :
    FamNat m q P (fun n => (SeqD.app τ (.xi m) pre R (info R).seq P' .zero).nat n) := by
  have hr : (info R).seq.dom = .big (.M m) := hRd
  have hRP := hRi.props
  have hMF := G.hMF
  have hρ := G.ht
  have hqF := G.hqF
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hRCρ : inC R q (.Xi m q) = true := G.pre_inCρ R (by simp)
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam τ (.M m) (.xi m) pre R (info R).seq .zero P' := ⟨_, rfl⟩
  have hγ0 : γ 0 = P' := by rw [hγdef]; exact gam_xi_M_zero
  have hγS : ∀ n, WNF (fundBig R (γ n)) →
      γ (n + 1) = .Xi m (xa pre .zero (fundBig R (γ n))) := by
    intro n hx
    rw [hγdef, gam_xi_M_succ, ← hγdef]
    exact congrArg (Tm.Xi m) (combine_xi m pre WNF.zero hx)
  have hfun : (fun n => (SeqD.app τ (.xi m) pre R (info R).seq P' .zero).nat n) = (fun n => γ (n + 1)) :=
    funext fun n => by rw [app_xi_M_nat hr hτ, hγdef]
  rw [hfun]
  -- 近似の引数の性質（`ξ < M_m`）
  have hxF : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (fundBig R ξ) := fun ξ hξ hξM => hRP.nf ξ hξ hξM
  have hgap : ∀ ξ, WNF ξ → Lt ξ (.M m) → ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R ξ) :=
    fun ξ hξ hξM v hv hne hlt => hRi.gapP G.hRp ξ v hξ hξM hv hne hlt
  have hxCM : ∀ ξ, WNF ξ → Lt ξ (.M m) → inC (fundBig R ξ) (xa pre .zero (fundBig R ξ)) (.M m) = true := by
    intro ξ hξ hξM
    by_cases hA0 : xa pre .zero (fundBig R ξ) = .zero
    · have hx0 : fundBig R ξ = .zero := by
        have h1 := G.hxA (hxF ξ hξ hξM)
        rw [hA0] at h1
        rcases h1 with e | h1
        · exact e
        · exact absurd h1 (not_lt_zero _)
      rw [hx0]; exact inC_zero _ _
    have hRC := G.pre_inC (hxF ξ hξ hξM) (hgap ξ hξ hξM) (hRi.pos ξ hξ hξM) G.hqC R (by simp)
    exact hRi.ub _ _ ξ (G.hAF (hxF ξ hξ hξM)) hA0 (Cut.of_wnf hMF) hξ hξM (inC_kTerm _ _ _) hRC
      (inC_of_lt_cut (Cut.of_wnf hMF) _ hξ hξM)
  have hxCρ : ∀ ξ, WNF ξ → Lt ξ (.Xi m q) → inC (fundBig R ξ) q (.Xi m q) = true := fun ξ hξ hξρ =>
    hRi.ub q _ ξ hqF G.hq0 (Cut.of_wnf hρ) hξ (lt_transY hξ hρ hMF hξρ hρM) (inC_kTerm _ _ _) hRCρ
      (inC_of_lt_cut (Cut.of_wnf hρ) _ hξ hξρ)
  -- 塔の項
  have key : ∀ n, WNF (γ n) ∧ Lt (γ n) (.Xi m q) := by
    intro n
    induction n with
    | zero => rw [hγ0]; exact ⟨hP'F, hP'ρ⟩
    | succ n ih =>
      have hγM := lt_transY ih.1 hρ hMF ih.2 hρM
      have hx := hxF _ ih.1 hγM
      rw [hγS n hx]
      exact ⟨G.nf hx (hRP.lt _ ih.1 hγM) (hgap _ ih.1 hγM) (hRi.pos _ ih.1 hγM) (hxCM _ ih.1 hγM),
        G.ltρ hx (hRP.lt _ ih.1 hγM) (hxCρ _ ih.1 ih.2) (inC_zero _ _)⟩
  have hγF : ∀ n, WNF (γ n) := fun n => (key n).1
  have hγρ : ∀ n, Lt (γ n) (.Xi m q) := fun n => (key n).2
  have hγM : ∀ n, Lt (γ n) (.M m) := fun n => lt_transY (hγF n) hρ hMF (hγρ n) hρM
  have hγS' : ∀ n, γ (n + 1) = .Xi m (xa pre .zero (fundBig R (γ n))) := fun n =>
    hγS n (hxF _ (hγF n) (hγM n))
  -- 塔は単調
  have hγm : ∀ n, Lt (γ n) (γ (n + 1)) := by
    intro n
    have hy : WNF (.Xi m (xa pre .zero (fundBig R (γ n)))) := by rw [← hγS' n]; exact hγF _
    rw [hγS' n]
    obtain ⟨-, -, hxC⟩ := G.parts (hxF _ (hγF n) (hγM n)) (hRP.lt _ (hγF n) (hγM n)) (xi_selfY hy)
    exact coll_xi0 hy (γ n) (hγF n) (hRi.lo _ _ (γ n) (Cut.of_wnf hy) (hγF n) (hγM n) hxC) (hγM n)
  have hγCl : ∀ n, Cl (.M m) (γ (n + 1)) := fun n => by
    rw [hγS' n]; exact Cl.of_xi (by rw [← hγS' n]; exact hγF _)
  -- 種は 0 番目の項未満
  have hy0F : WNF (.Xi m (xa pre .zero (fundBig R P'))) := by rw [← hγ0, ← hγS' 0]; exact hγF 1
  have hP'y : Lt P' (.Xi m (xa pre .zero (fundBig R P'))) := by
    have h1 := hγm 0
    rw [hγS' 0, hγ0] at h1
    exact h1
  -- `famNat_xa` に渡す
  have hfun2 : (fun n => γ (n + 1)) = (fun n => .Xi m (xa pre .zero (fundBig R (γ n)))) :=
    funext hγS'
  rw [hfun2]
  have hCγ : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → ∀ n, inC (γ n) g d = true := by
    intro g d hg hg0 hd hρC hρd hPC n
    rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, hqg⟩
    · exact absurd h1 hρd
    have hRC : inC R g d = true := inC_of_mem_summands hqF hqC G.hRq
    induction n with
    | zero => rw [hγ0]; exact hP'ub g d hg hg0 hd hρC hρd hPC
    | succ n ih =>
      rw [hγS' n]
      by_cases hlt : Lt (.Xi m (xa pre .zero (fundBig R (γ n)))) d
      · exact inC_of_lt_node (Or.inl ⟨_, _, rfl⟩) hlt
      · have hx := hxF _ (hγF n) (hγM n)
        refine inC_xi_iff.mpr (Or.inr ⟨G.inC_A hx (fun s hs => inC_of_mem_summands hqF hqC (G.hpreq hs))
          (inC_zero _ _) (hRi.ub g d (γ n) hg hg0 hd (hγF n) (hγM n) (inC_kTerm _ _ _) hRC ih),
          lt_transY (G.hAF hx) hqF hg (G.hAq hx (hRP.lt _ (hγF n) (hγM n))) hqg⟩)
  refine famNat_xa G (fun n => fundBig R (γ n)) (fun n => hxF _ (hγF n) (hγM n))
    (fun n => hRP.lt _ (hγF n) (hγM n)) (fun n => hgap _ (hγF n) (hγM n))
    (fun n => hRi.pos _ (hγF n) (hγM n))
    (fun n => hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγM _))
    (fun n => hxCM _ (hγF n) (hγM n)) (fun n => hxCρ _ (hγF n) (hγρ n)) (zero_lt (by intro e; cases e))
    (fun g d n hg hg0 hd hρC hρd hPC => ⟨?_, inC_zero _ _⟩) (fun g d n hg hg0 hd hC => ?_)
    (fun c' N _ hc' hc'R _ _ _ hfr => ?_)
    (fun c h1 h2 h3 h4 => by
      show Lt _ (.Xi m (xa pre .zero (fundBig R (γ 0)))); rw [hγ0]
      rcases hrest c h1 h2 h3 h4 with h | h
      · exact lt_of_le_of_ltY h1 hP'F hy0F h hP'y
      · exact h)
    (fun p hp => ?_)
  · rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, -⟩
    · exact absurd h1 hρd
    exact hRi.ub g d (γ n) hg hg0 hd (hγF n) (hγM n) (inC_kTerm _ _ _)
      (inC_of_mem_summands hqF hqC G.hRq) (hCγ g d hg hg0 hd hρC hρd hPC n)
  · -- 2 点の上界
    have hγ1C := hRi.lo g d (γ (n + 1)) hd (hγF _) (hγM _) hC
    by_cases hlt : Lt (γ (n + 1)) d
    · exact hRi.ub2 g d (γ n) (γ (n + 1)) hg hg0 hd (hγF n) (hγF _) (hγm n) (hγM _)
        (Or.inl (inC_kTerm _ _ _))
        (inC_of_lt_cut hd g (hγF n) (hd _ _ (hγF n) (hγF _) (hγm n) hlt)) hC
    · rw [hγS' n] at hγ1C hlt
      rcases inC_xi_iff.mp hγ1C with h1 | ⟨hAC, -⟩
      · exact absurd h1 hlt
      exact (G.parts (hxF _ (hγF n) (hγM n)) (hRP.lt _ (hγF n) (hγM n)) hAC).2.2
  · -- 引数の共終性
    refine ⟨N + 1, hRi.clo hc' hc'R (hγF _) (hγM _) (hγCl N) (fun f hf => ?_)⟩
    have h1 := hfr f hf
    rw [← hγS' N] at h1
    exact h1
  · -- 種
    show Lt p (.Xi m (xa pre .zero (fundBig R (γ 0))))
    rw [hγ0]
    rcases hseed p hp with ⟨hpF, hpP⟩ | h
    · exact lt_of_le_of_ltY hpF hP'F hy0F hpP hP'y
    · exact h

/-! ### 列を一つずらす（`R` の列が `ω` 型） -/

/-- 列を一つずらした近似 `Ξ_m(pre ⊕ (P' # R[n+1]))` の族の列 -/
theorem famNat_app_shift {m : Nat} {q P' R τ : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (hRd : dom R = .omega) (hRi : NatInv R)
    (hPρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) → Lt (.Xi m c) (.Xi m (xa pre P' (fundNat R 1))))
    (hseed : ∀ p, P = some p → Lt p (.Xi m (xa pre P' (fundNat R 1)))) :
    FamNat m q P (fun n => (SeqD.app τ (.xi m) pre R (.shift (info R).seq) P' .zero).nat n) := by
  have hr : (SeqD.shift (info R).seq).dom = .omega := hRd
  have hRP := hRi.props
  have hfun : (fun n => (SeqD.app τ (.xi m) pre R (.shift (info R).seq) P' .zero).nat n) =
      (fun n => .Xi m (xa pre P' (fundNat R (n + 1)))) :=
    funext fun n => app_xi_nat hr G.hPF (hRP.nf (n + 1))
  rw [hfun]
  have hqF := G.hqF
  have hRCρ : inC R q (.Xi m q) = true := G.pre_inCρ R (by simp)
  refine famNat_xa G (fun n => fundNat R (n + 1)) (fun n => hRP.nf _) (fun n => hRP.lt _)
    (fun n => hRi.gap _) (fun n h0 => absurd h0 (hRi.pos _)) (fun n => hRP.mono _) (fun n => ?_)
    (fun n => hRi.ub q _ _ hqF G.hq0 (Cut.of_wnf G.ht) hRCρ) hPρ
    (fun g d n hg hg0 hd hρC hρd hPC => ?_) (fun g d n hg hg0 hd => hRi.ub2 g d _ hg hg0 hd)
    (fun c' N _ hc' hc'R _ _ _ _ => ?_) hrest hseed
  · have hRC := G.pre_inC (hRP.nf (n + 1)) (hRi.gap _) (fun h0 => absurd h0 (hRi.pos _)) G.hqC R
      (by simp)
    exact hRi.ub _ _ _ (G.hAF (hRP.nf _)) (G.xa0 (hRP.nf _) (hRi.pos _)) (Cut.of_wnf G.hMF) hRC
  · rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, -⟩
    · exact absurd h1 hρd
    exact ⟨hRi.ub g d _ hg hg0 hd (inC_of_mem_summands hqF hqC G.hRq), hP'ub g d hg hg0 hd hρC hρd hPC⟩
  · obtain ⟨n, hn⟩ := hRP.cof c' hc' hc'R
    exact ⟨n, lt_of_le_of_ltY hc' (hRP.nf n) (hRP.nf _) hn (hRP.mono n)⟩

/-! ### `Ω` の塔 -/

/-- `Ω` の塔 `y_n = tower s (n+1)` の族の列：族の元が全て `s` 以下なら閉じている -/
theorem famNat_tower {m : Nat} {q s : Tm} {P : Option Tm} (hρ : WNF (.Xi m q)) (hsF : WNF s)
    (hsρ : Lt s (.Xi m q)) (hbot : Le (floorLev m) s)
    (hseed : ∀ p, P = some p → WNF p ∧ Le p s)
    (hclo : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q → Le (.Xi m c) s)
    (hsub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC s g d = true) :
    FamNat m q P (fun n => tower s (n + 1)) := by
  have hOF : IsOF (.Xi m q) := Or.inl ⟨m, q, rfl⟩
  have hTF := wnf_tower hsF
  have hs1 : Lt s (tower s 1) := tower_lt_succ hsF 0
  refine ⟨fun n => hTF _, fun n => rfl, fun n => tower_lt_succ hsF _,
    fun n => tower_lt_OF hsF hρ hOF hsρ _, fun p hp => ?_, ?_, fun e N he hlt => ⟨N + 1, ?_⟩,
    fun c N hc hcρ hcq _ => ⟨0, ?_⟩,
    fun g d n hg hg0 hd hρC hρd hPC => inC_tower hg0 (hsub g d hg hg0 hd hρC hρd hPC) _,
    fun g d n _ _ _ hC => ?_⟩
  · obtain ⟨hpF, hps⟩ := hseed p hp
    exact lt_of_le_of_ltY hpF hsF (hTF 1) hps hs1
  · exact lt_of_le_of_ltY (wnf_kTerm _) hsF (hTF 1) hbot hs1
  · show Lt (.Om e) (.Om (succT (tower s (N + 1))))
    exact lt_om_iffG.mpr (lt_transY he (hTF _) (succT_WNF (hTF _)) hlt (lt_succT _))
  · exact lt_of_le_of_ltY hc hsF (hTF 1) (hclo c hc hcρ hcq) hs1
  · have h1 : inC (.Om (succT (tower s (n + 1)))) g d = true := hC
    rw [inC_om] at h1
    exact inC_of_succT h1

/-! ### `q = M_m⁺`（仮想的な塔 `g_k`） -/

theorem omReg_succM (m : Nat) : omReg (.plus (.M m) one) := Or.inr rfl

theorem info_seq_succM (m : Nat) :
    (info (succM m)).seq = .reg (succM m) (.Psi (succM m) .zero) [] := by
  show (info (.Om (.plus (.M m) one))).seq = _
  rw [info_seq_om, ite_eq_left (omReg_succM m)]
  rfl

theorem outsideMode_xi {τ σ : Tm} {m : Nat} (hM : ∀ k, σ ≠ .M k) (hne : σ ≠ τ) (pre : List Tm)
    (R : Tm) : outsideMode τ σ (.xi m) pre R = true := by
  cases σ with
  | M k => exact absurd rfl (hM k)
  | _ => simp [outsideMode, Gen.tgt?, hne]

theorem gam_xi_out_zero {τ σ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hM : ∀ k, σ ≠ .M k)
    (hne : σ ≠ τ) : gam τ σ (.xi m) pre R r .zero P' 0 =
      if validR σ (oadd (ofSummands pre) (r.big .zero)) then .zero
      else col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big .zero))) 0 := by
  cases σ with
  | M k => exact absurd rfl (hM k)
  | _ => simp only [gam, canonK_notM hM, outsideMode_xi hM hne, Bool.false_eq_true, ↓reduceIte]

theorem gam_xi_out_succ {τ σ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hM : ∀ k, σ ≠ .M k)
    (hne : σ ≠ τ) (k : Nat) : gam τ σ (.xi m) pre R r .zero P' (k + 1) =
      col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big (gam τ σ (.xi m) pre R r .zero P' k)))) k := by
  cases σ with
  | M j => exact absurd rfl (hM j)
  | _ => simp only [gam, canonK_notM hM, outsideMode_xi hM hne, Bool.false_eq_true, ↓reduceIte]

theorem app_xi_out_nat {τ σ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hM : ∀ k, σ ≠ .M k)
    (hne : σ ≠ τ) (hr : r.dom = .big σ) (hστ : ltB σ τ = false) (n : Nat) :
    (SeqD.app τ (.xi m) pre R r P' .zero).nat n =
      .Xi m (combine (.xi m) pre .zero P' (r.big (gam τ σ (.xi m) pre R r .zero P' n))) := by
  simp only [SeqD.nat, hr, hστ, Bool.false_eq_true, ↓reduceIte, argOf, canonK_notM hM,
    outsideMode_xi hM hne, Gen.ap]

theorem succM_ne_M (m k : Nat) : succM m ≠ .M k := fun e => by cases e
theorem succM_ne_xi (m : Nat) : succM m ≠ .Xi m (succM m) := fun e => by cases e

theorem gam_xi_S {m : Nat} {P' : Tm} (hm : 1 ≤ m) (k : Nat) :
    gam (.Xi m (succM m)) (succM m) (.xi m) [] (succM m) (info (succM m)).seq .zero P' k = virtG m k := by
  induction k with
  | zero =>
    have hv : ∀ x, validR (succM m) x = true := fun _ => rfl
    rw [gam_xi_out_zero (succM_ne_M m) (succM_ne_xi m)]
    simp only [hv, ↓reduceIte]
    rfl
  | succ k ih =>
    rw [gam_xi_out_succ (succM_ne_M m) (succM_ne_xi m), ih, info_seq_succM]
    show col (succM m) (oadd (ofSummands []) (oadd (adjOf (succM m) []) (oadd (.Psi (succM m) .zero) (virtG m k)))) k = virtG m (k + 1)
    rw [show adjOf (succM m) [] = .zero from rfl, zero_oadd (virtE_F hm k),
      show ofSummands ([] : List Tm) = .zero from rfl, zero_oadd (virtE_F hm k)]
    simp only [col, validR, argR?]
    rfl

/-- `q = M_m⁺` の仮想的な塔の族の列：`y_n = Ξ_m(P' # (ψ₀ ⊕ g_n))` -/
theorem famNat_app_S {m : Nat} {P' : Tm} {P : Option Tm}
    (G : XG m (succM m) P' [] [] (succM m)) (hPρ : Lt P' (.Xi m (succM m)))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m (succM m)) g d = true →
      ¬ Lt (.Xi m (succM m)) d → (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hseed : ∀ p, P = some p → (WNF p ∧ Le p P') ∨ Lt p (.Xi m (xa [] P' (virtE m 0)))) :
    FamNat m (succM m) P (fun n =>
      (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq P' .zero).nat n) := by
  have hm := G.hm
  have hρ := G.ht
  have hSF := WNF.succM hm
  have hr : (info (succM m)).seq.dom = .big (succM m) := by rw [info_seq_succM]; rfl
  have hρS : Lt (.Xi m (succM m)) (succM m) :=
    lt_transY hρ (WNF.M' hm) hSF (xi_lt_M _) (M_lt_succM hm)
  have hστ : ltB (succM m) (.Xi m (succM m)) = false := by
    cases e : ltB (succM m) (.Xi m (succM m)) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hSF hρS)
  have hEF := virtE_F hm
  have hfun : (fun n =>
      (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq P' .zero).nat n) =
      (fun n => .Xi m (xa [] P' (virtE m n))) := by
    funext n
    rw [app_xi_out_nat (succM_ne_M m) (succM_ne_xi m) hr hστ, gam_xi_S hm, info_seq_succM]
    exact congrArg (Tm.Xi m) (combine_xi m [] G.hPF (hEF n))
  rw [hfun]
  -- `virtE` の所属
  have hEC : ∀ n g d, Lt .zero g → (∀ j, j < n → Lt (virtE m j) g) → inC (virtE m n) g d = true :=
    fun n g d h0 h => inC_oadd (wnf_psi0M hm) (virtG_F hm n) (inC_psi0M h0) (inC_virtG hm h0 n h)
  have hE0 : ∀ n, virtE m n ≠ .zero := fun n =>
    oadd_ne_zero_left (wnf_psi0M hm) (virtG_F hm n) (by intro e; cases e)
  have hgapS : ∀ n v, v ∈ subs (succM m) → v ≠ succM m → Lt v (succM m) → Lt v (virtE m n) := by
    intro n v hv hne hlt
    have hv' : v ∈ subs (.plus (.M m) one) := by
      have e : subs (succM m) = succM m :: subs (.plus (.M m) one) := rfl
      rw [e, List.mem_cons] at hv
      rcases hv with e | hv
      · exact absurd e hne
      · exact hv
    exact lt_of_lt_of_leY (hSF.of_mem_subs hv) (wnf_psi0M hm) (hEF n)
      (sub_lt_base_om hSF (omReg_succM m) .zero v hv' (hSF.of_mem_subs hv) hlt)
      (le_oadd_leftW (wnf_psi0M hm) (virtG_F hm n))
  have hxCM : ∀ n, inC (virtE m n) (xa [] P' (virtE m n)) (.M m) = true := by
    intro n
    have hA := G.hAF (hEF n)
    have hA0 := G.xa0 (hEF n) (hE0 n)
    exact hEC n _ _ (zero_lt hA0) (fun j hj =>
      lt_of_lt_of_leY (hEF j) (hEF n) hA (virtE_lt_of hm hj) (G.hxA (hEF n)))
  have hy0F : WNF (.Xi m (xa [] P' (virtE m 0))) :=
    G.nf (hEF 0) (virtE_lt hm 0) (hgapS 0) (fun h0 => absurd h0 (hE0 0)) (hxCM 0)
  have hP'y := G.seed_lt (hEF 0) (virtE_lt hm 0) hy0F
  refine famNat_xa G (fun n => virtE m n) hEF (virtE_lt hm) hgapS
    (fun n h0 => absurd h0 (hE0 n)) (virtE_mono hm) hxCM (fun n => ?_) hPρ
    (fun g d n hg hg0 hd hρC hρd hPC => ?_) (fun g d n hg hg0 hd hC => ?_)
    (fun c' N g hc' hc'R hg hgq hc'C _ => ?_) (fun c _ _ hcq hcT => absurd hcq ?_)
    (fun p hp => (hseed p hp).elim (fun h => lt_of_le_of_ltY h.1 G.hPF hy0F h.2 hP'y) id)
  · exact hEC n _ _ (zero_lt (by intro e; cases e)) (fun j _ => virtE_lt hm j)
  · rcases inC_xi_iff.mp hρC with h1 | ⟨-, hSg⟩
    · exact absurd h1 hρd
    exact ⟨hEC n g d (lt_transY WNF.zero hSF hg (zero_lt (by intro e; cases e)) hSg)
      (fun j _ => lt_transY (hEF j) hSF hg (virtE_lt hm j) hSg), hP'ub g d hg hg0 hd hρC hρd hPC⟩
  · -- 2 点の上界
    have hG1 : inC (virtG m (n + 1)) g d = true := inC_of_oadd_right (wnf_psi0M hm) (virtG_F hm _) hC
    rw [virtG_succ] at hG1
    have hyF : WNF (Tm.Psi (succM m) (virtE m n)) := by rw [← virtG_succ]; exact virtG_F hm _
    by_cases hlt : Lt (Tm.Psi (succM m) (virtE m n)) d
    · have h1 : Lt (virtE m n) (.Psi (succM m) (virtE m n)) :=
        coll_psiY hyF (hEF n) hyF.psi.Ca (virtE_lt hm n)
      exact inC_of_lt_cut hd g (hEF n) (hd _ _ (hEF n) hyF h1 hlt)
    · rcases inC_psi_iff.mp hG1 with h1 | ⟨-, hEC', -⟩
      · exact absurd h1 hlt
      · exact hEC'
  · -- 引数の共終性
    obtain ⟨n, hn⟩ := virtG_hull hm hg hgq c' hc' hc'R hc'C
    exact ⟨n + 1, lt_of_lt_of_leY hc' (virtG_F hm _) (hEF _) hn
      (le_oadd_right (wnf_psi0M hm) (virtG_F hm _))⟩
  · exact hcT

end MahloOCF.FS
