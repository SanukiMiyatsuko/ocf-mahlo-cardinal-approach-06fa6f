import Mahlo.FS.XiFam

/-! 目標の族 `Ξ_m(q)` の閉包（`famSeq`・`mahloVK`）の `ω` 型の列の仕様 `FamNat`。

列の項 `y_n` は `Ξ_m(q)` 未満の主要項で、単調、種より大きく、`M_{m-1}` より大きい。`Ω` と族
（`Ξ_m(c)`、`c < q`、成分が列の下）について閉じている（`clo`）。上界 `ub`・2 点の上界 `ub2` も持つ。

近似 `y_n = Ξ_m(pre ⊕ (P # x_n))`（`x_n` は `R` の列の項）からの構成（`famNat_xa`）：`R` の列の
性質と、引数の共終性（`R` 未満の `c'` は `x_n` の下）、`T = pre ⊕ R` 以上の `c` の評価から。 -/

namespace MahloOCF.FS

open Tm

/-- `Ξ_m(q)` の族の閉包の `ω` 型の列の性質（種 `P`） -/
structure FamNat (m : Nat) (q : Tm) (P : Option Tm) (y : Nat → Tm) : Prop where
  F : ∀ n, WNF (y n)
  prin : ∀ n, isPrincipal (y n) = true
  mono : ∀ n, Lt (y n) (y (n + 1))
  ltρ : ∀ n, Lt (y n) (.Xi m q)
  seed : ∀ p, P = some p → Lt p (y 0)
  bot : Lt (floorLev m) (y 0)
  om : ∀ e N, WNF e → Lt e (y N) → ∃ n, Lt (.Om e) (y n)
  clo : ∀ c N, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
    (∀ w, w ∈ fr (.M m) c → Lt w (y N)) → ∃ n, Lt (.Xi m c) (y n)
  ub : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
    (∀ p, P = some p → inC p g d = true) → inC (y n) g d = true
  ub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC (y (n + 1)) g d = true → inC (y n) g d = true

/-- `M_{m-1} < Ξ_m(A)` -/
theorem floorLev_lt_xi {m : Nat} {A : Tm} (hy : WNF (.Xi m A)) : Lt (floorLev m) (.Xi m A) := by
  have hm := hy.xi.1
  unfold floorLev kTerm
  split
  · exact zero_lt (by intro e; cases e)
  · exact bot_ltY rfl (by simp only [lev]; omega) rfl rfl hy

theorem FamNat.mono_le {m : Nat} {q : Tm} {P : Option Tm} {y : Nat → Tm} (h : FamNat m q P y)
    {i k : Nat} (hik : i ≤ k) : Le (y i) (y k) := seq_mono_le h.F h.mono hik

/-! ### 近似 `Ξ_m(pre ⊕ (P' # x_n))` の列 -/

/-- 近似 `y_n = Ξ_m(pre ⊕ (P' # x_n))` の列の仕様 -/
theorem famNat_xa {m : Nat} {q P' R : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (x : Nat → Tm) (hxF : ∀ n, WNF (x n)) (hxR : ∀ n, Lt (x n) R)
    (hgap : ∀ n v, v ∈ subs R → v ≠ R → Lt v R → Lt v (x n))
    (hpos : ∀ n, x n = .zero → ∀ v, v ∈ subs R → v = R)
    (hxm : ∀ n, Lt (x n) (x (n + 1)))
    (hxCM : ∀ n, inC (x n) (xa pre P' (x n)) (.M m) = true)
    (hxCρ : ∀ n, inC (x n) q (.Xi m q) = true)
    (hPρ : Lt P' (.Xi m q))
    (hxub : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC (x n) g d = true ∧ inC P' g d = true)
    (hxub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC (x (n + 1)) g d = true → inC (x n) g d = true)
    (hcof : ∀ c' N g, WNF c' → Lt c' R → WNF g → Lt g q → inC c' g (.M m) = true →
      (∀ w, w ∈ fr (.M m) c' → Lt w (.Xi m (xa pre P' (x N)))) → ∃ n, Lt c' (x n))
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) → Lt (.Xi m c) (.Xi m (xa pre P' (x 0))))
    (hseed : ∀ p, P = some p → Lt p (.Xi m (xa pre P' (x 0)))) :
    FamNat m q P (fun n => .Xi m (xa pre P' (x n))) := by
  have hm := G.hm
  have hMF := G.hMF
  have hqF := G.hqF
  have hρ := G.ht
  have hPF := G.hPF
  have hpreF := G.hpreF
  have hAF : ∀ n, WNF (xa pre P' (x n)) := fun n => G.hAF (hxF n)
  have hyF : ∀ n, WNF (.Xi m (xa pre P' (x n))) := fun n =>
    G.nf (hxF n) (hxR n) (hgap n) (hpos n) (hxCM n)
  have hAm : ∀ n, Lt (xa pre P' (x n)) (xa pre P' (x (n + 1))) := fun n =>
    G.hAmono (hxF n) (hxF (n + 1)) (hxm n)
  have hx0 : ∀ n, x (n + 1) ≠ .zero := fun n e => by
    have h := hxm n; rw [e] at h; exact not_lt_zero _ h
  have hy0 : ∀ n, nsum P' (x (n + 1)) ≠ .zero := fun n e => by
    have h1 := le_nsum_right hPF (hxF (n + 1))
    rw [e] at h1
    rcases h1 with e' | h1
    · exact hx0 n e'
    · exact not_lt_zero _ h1
  have hA0 : ∀ n, xa pre P' (x (n + 1)) ≠ .zero := fun n e => by
    have h1 := G.hxA (hxF (n + 1))
    rw [e] at h1
    rcases h1 with e' | h1
    · exact hx0 n e'
    · exact not_lt_zero _ h1
  have hym : ∀ n, Lt (.Xi m (xa pre P' (x n))) (.Xi m (xa pre P' (x (n + 1)))) := by
    intro n
    obtain ⟨-, -, hx1C⟩ := G.parts (hxF (n + 1)) (hxR (n + 1)) (xi_selfY (hyF (n + 1)))
    exact G.lt2 (hxF n) (hxF (n + 1)) (hxR (n + 1)) (hxm n) (hyF (n + 1))
      (hxub2 _ _ n (hAF (n + 1)) (hA0 n) (Cut.of_wnf (hyF (n + 1))) hx1C)
  have hylt : ∀ n, Lt (.Xi m (xa pre P' (x n))) (.Xi m q) := fun n =>
    G.ltρ (hxF n) (hxR n) (hxCρ n) (inC_of_lt_cut (Cut.of_wnf hρ) _ hPF hPρ)
  have hOF : ∀ n, IsOF (.Xi m (xa pre P' (x n))) := fun n => Or.inl ⟨_, _, rfl⟩
  refine ⟨hyF, fun n => rfl, hym, hylt, hseed, floorLev_lt_xi (hyF 0),
    fun e N heF he => ⟨N, (lt_om_OFG (hOF N) (hyF N)).mpr he⟩, ?_, ?_, ?_⟩
  · -- 族について閉じている
    intro c N hc hcρ hcq hfr
    have hcF := hc.xi.2.1
    by_cases hcT : Lt c (ofSummands (pre ++ [R]))
    · rcases lt_split G.hTF G.hsT hcF hcT with hle | ⟨c', hc', hc'0, hc'R, hsc, hce⟩
      · -- `c ≤ pre`
        refine ⟨N + 1, xi_step hc (hyF (N + 1)) ?_ (fun w hw => lt_transY
          (hcF.of_mem_subs (fr_spec hw).1) (hyF N) (hyF _) (hfr w hw) (hym N))⟩
        exact lt_of_le_of_ltY hcF hpreF (hAF _) hle (lt_oadd_left hpreF (G.hyF (hxF _)) (hy0 N))
      · -- `c = pre ⊕ c'`、`c' < R`
        have hfr' : ∀ w, w ∈ fr (.M m) c' → Lt w (.Xi m (xa pre P' (x N))) := fun w hw =>
          hfr w (fr_sub_of_summands (fun u hu => by rw [hsc]; exact List.mem_append_right _ hu) hw)
        have hc'C : inC c' c (.M m) = true := by
          rw [inC_iff_summandsW hc']
          intro s hs
          exact inC_of_mem_summands hcF hc.xi.2.2.2 (by rw [hsc]; exact List.mem_append_right _ hs)
        obtain ⟨n, hn⟩ := hcof c' N c hc' hc'R hcF hcq hc'C hfr'
        refine ⟨max n N, xi_step hc (hyF _) ?_ (fun w hw => lt_of_lt_of_leY
          (hcF.of_mem_subs (fr_spec hw).1) (hyF N) (hyF _) (hfr w hw)
          (seq_mono_le hyF hym (Nat.le_max_right n N)))⟩
        rw [hce]
        have h1 : Lt c' (nsum P' (x (max n N))) :=
          lt_of_lt_of_leY hc' (hxF _) (G.hyF (hxF _))
            (lt_of_lt_of_leY hc' (hxF n) (hxF _) hn (seq_mono_le hxF hxm (Nat.le_max_left n N)))
            (le_nsum_right hPF (hxF _))
        exact oadd_lt_oadd hpreF hc' (G.hyF (hxF _)) h1
    · exact ⟨0, hrest c hc hcρ hcq hcT⟩
  · -- 上界
    intro g d n hg hg0 hd hρC hρd hPC
    by_cases hlt : Lt (.Xi m (xa pre P' (x n))) d
    · exact inC_of_lt_node (Or.inl ⟨_, _, rfl⟩) hlt
    rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, hqg⟩
    · exact absurd h1 hρd
    obtain ⟨hxC, hP'C⟩ := hxub g d n hg hg0 hd hρC hρd hPC
    refine inC_xi_iff.mpr (Or.inr ⟨G.inC_A (hxF n) (fun s hs => ?_) hP'C hxC,
      lt_transY (hAF n) hqF hg (G.hAq (hxF n) (hxR n)) hqg⟩)
    exact inC_of_mem_summands hqF hqC (G.hpreq hs)
  · -- 2 点の上界
    intro g d n hg hg0 hd hC
    by_cases hlt : Lt (.Xi m (xa pre P' (x (n + 1)))) d
    · exact inC_of_lt_cut hd g (hyF n) (hd _ _ (hyF n) (hyF _) (hym n) hlt)
    rcases inC_xi_iff.mp hC with h1 | ⟨hAC, hAg⟩
    · exact absurd h1 hlt
    obtain ⟨hpre, hP'C, hx1C⟩ := G.parts (hxF (n + 1)) (hxR (n + 1)) hAC
    exact inC_xi_iff.mpr (Or.inr ⟨G.inC_A (hxF n) hpre hP'C (hxub2 g d n hg hg0 hd hx1C),
      lt_transY (hAF n) (hAF _) hg (hAm n) hAg⟩)

end MahloOCF.FS
