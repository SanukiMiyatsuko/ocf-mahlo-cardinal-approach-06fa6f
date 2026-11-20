import Mahlo.FS.FamBig

/-! `Ξ_m(q)` への崩壊 `t = Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の列：種 `p = Ψ_{Ξ_m(q)}(X')` の上の族の閉包。

* 種 `p` は `SeedHyp` を満たす（`seedHyp_valid`）：`q ∈ C(q, p)`（`p` の底の条件）を段 `c` に移す。
* 共終性（`cof_nat`）：`t` 未満の節点 `x` は、階が `m` 未満なら列の下。`Ξ_m(c)` は `c < q` なら族の閉包
  （`FamNat.clo`）、`q < c` なら `p` 未満。`Ψ_κ(b)` は `κ < Ξ_m(q)` なら `κ` が列の下、`κ = Ξ_m(q)` なら
  `p` 以下、`κ > Ξ_m(q)` なら底の条件を満たさないので `p` 未満。 -/

namespace MahloOCF.FS

open Tm

/-! ### 先頭部分で分けた加数 -/

/-- `ofSummands L₁ ≤ c < q`（`summands q = L₁ ++ L₂`）なら、`c` の加数は `L₁` と、`L₂` のある元以下のもの -/
theorem summands_between {c q : Tm} {L₁ L₂ : List Tm} (hc : WNF c) (hq : WNF q)
    (hsq : summands q = L₁ ++ L₂) (hcT : ¬ Lt c (ofSummands L₁)) (hcq : Lt c q) :
    ∃ l', summands c = L₁ ++ l' ∧ ∀ u, u ∈ l' → ∃ v, v ∈ L₂ ∧ Le u v := by
  cases hL : L₁.getLast? with
  | none =>
    have e := List.getLast?_eq_none_iff.mp hL
    subst e
    exact ⟨summands c, rfl, tail_le_of_lt hc hq rfl hsq hcq⟩
  | some R =>
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hL
    subst hpre
    have hN : NFL (pre ++ R :: L₂) := by
      have := nfl_summands hq; rw [hsq] at this; simpa using this
    have hT := nfl_prefix hN
    have hsT : summands (ofSummands (pre ++ [R])) = pre ++ [R] :=
      summands_ofSummands _ (nfl_principal hT)
    have h1 : cmpList (summands c) (pre ++ [R]) ≠ .lt := by
      intro h; apply hcT; unfold Lt; rw [cmp_eq, hsT]; exact h
    have h2 : cmpList (summands c) (pre ++ R :: L₂) = .lt := by
      have := hcq; unfold Lt at this; rw [cmp_eq, hsq] at this; simpa using this
    obtain ⟨l', hl'⟩ := prefix_of_between pre R L₂ (summands c) hN.1 (nfl_summands hc).1 h1 h2
    have hc' : summands c = (pre ++ [R]) ++ l' := by rw [hl']; simp
    exact ⟨l', hc', tail_le_of_lt hc hq hc' hsq hcq⟩

/-! ### 種 `p = Ψ_{Ξ_m(q)}(X')` -/

/-- `q ∈ C(q, p)`、`q < c`、`p ≤ x` なら `q ∈ C(c, x)` -/
theorem inC_seed_up {q p c x : Tm} (hqF : WNF q) (hpF : WNF p) (hxF : WNF x) (hcF : WNF c)
    (hqp : inC q q p = true) (hqc : Lt q c) (hpx : Le p x) : inC q c x = true :=
  inC_mono_node q q p c x hqp
    (fun _ hv _ hvp => lt_of_lt_of_leY (hqF.of_mem_subs hv) hpF hxF hvp hpx)
    (fun _ hv _ hvq => lt_transY (hqF.of_mem_subs hv) hqF hcF hvq hqc)

/-- 種 `p = Ψ_{Ξ_m(q)}(X')` は `SeedHyp` を満たす -/
theorem seedHyp_valid {m : Nat} {q X : Tm} (hp : WNF (.Psi (.Xi m q) X)) :
    SeedHyp m q (.Psi (.Xi m q) X) := by
  intro L₁ L₂ hsq hL₂ c hc hcρ hcq hcT
  have hρ := hp.psi.piF
  have hqF := hρ.xi.2.1
  have hcF := hc.xi.2.1
  obtain ⟨hk, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hp)
  refine Or.inr ((lt_xi_psi_iff (π := .Xi m q) (n := m) rfl).mpr ⟨?_, ?_⟩)
  · rw [swapY hc hρ]
    have : cmp (.Xi m c) (.Xi m q) = .lt := hcρ
    rw [this]; rfl
  refine (baseOf_xi_iff m c _).mpr ⟨hk, ?_⟩
  obtain ⟨l', hsc, hl'⟩ := summands_between hcF hqF hsq hcT hcq
  refine (inC_iff_summandsW hcF).mpr (fun u hu => ?_)
  rw [hsc] at hu
  rcases List.mem_append.mp hu with hu | hu
  · -- `L₁` の加数：段 `q` から段 `c` へ（大きさの議論）
    have huq : u ∈ summands q := by rw [hsq]; exact List.mem_append_left _ hu
    have huF := (summands_WNF q hqF u huq).1
    refine inC_mono_node u q _ c _ (inC_of_mem_summands hqF hqC huq) (fun _ _ _ h => h)
      (fun v hv hvs hvq => ?_)
    have hvF := huF.of_mem_subs hv
    -- `v < ofSummands L₁ ≤ c`
    cases hL : L₁.getLast? with
    | none => rw [List.getLast?_eq_none_iff.mp hL] at hu; cases hu
    | some R =>
      obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hL
      rw [hpre] at hu hsq hcT
      have hsq' : summands q = pre ++ R :: L₂ := by rw [hsq]; simp
      have h1 := lt_T_of_sub hqF hsq' hu hv (ne_of_size_lt hvs) hvF hvq
      have hTF : WNF (ofSummands (pre ++ [R])) := wnf_ofSummands (nfl_prefix (by
        rw [← hsq']; exact nfl_summands hqF))
      exact lt_of_lt_of_leY hvF hTF hcF h1 (le_of_not_ltY hcF hTF hcT)
  · -- 後ろの加数は `p` 未満
    obtain ⟨v, hv, huv⟩ := hl' u hu
    have hvq : v ∈ summands q := by rw [hsq]; exact List.mem_append_right _ hv
    have hvF := (summands_WNF q hqF v hvq).1
    have huF := (summands_WNF c hcF u (by rw [hsc]; exact List.mem_append_right _ hu)).1
    have hvp : Lt v (.Psi (.Xi m q) X) := by
      rcases hL₂ v hv with e | h
      · exfalso
        have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands hvq)
        rw [e] at h1
        simp only [Tm.size] at h1
        omega
      · exact h
    exact inC_of_lt_cut (Cut.of_wnf hp) _ huF (lt_of_le_of_ltY huF hvF hp huv hvp)

/-- `t = Ψ_{Ξ_m(q)}(X'+1)` 未満の `Ξ_m(c)`（`q < c`、`q ∉ C(c, Ξ_m(c))`）は種 `p = Ψ_{Ξ_m(q)}(X')` 未満 -/
theorem xi_lt_seed_of_gt {m : Nat} {q c X : Tm} (hpF : WNF (.Psi (.Xi m q) X)) (hqF : WNF q)
    (hx : WNF (.Xi m c)) (hqC : inC q q (.Psi (.Xi m q) X) = true) (hqc : Lt q c)
    (hnC : inC q c (.Xi m c) = false) : Lt (.Xi m c) (.Psi (.Xi m q) X) := by
  rcases triY hx hpF with h | e | h
  · exact h
  · cases e
  · exfalso
    have := inC_seed_up hqF hpF hx hx.xi.2.1 hqC hqc (Or.inr h)
    rw [this] at hnC; cases hnC

/-- `Ξ_m(q)` 未満の `Ψ_κ(b)`（`κ > Ξ_m(q)`、同じ階）は種 `p` 未満か `M_{m-1}` 以下 -/
theorem psi_gt_lt_seed {m : Nat} {q X κ b : Tm} (hpF : WNF (.Psi (.Xi m q) X)) (hx : WNF (.Psi κ b))
    (hlκ : lev κ = m) (hρκ : Lt (.Xi m q) κ) (hxρ : Lt (.Psi κ b) (.Xi m q)) :
    Lt (.Psi κ b) (.Psi (.Xi m q) X) ∨ Le (.Psi κ b) (kTerm (m - 1)) := by
  have hρ := hpF.psi.piF
  have hρT := hpF.psi.tgt
  have hqF := hρ.xi.2.1
  obtain ⟨-, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hpF)
  have hnb := not_base_of_lt_tgtY hx hρ hρT hlκ hρκ hxρ
  by_cases hkx : Lt (kTerm (m - 1)) (.Psi κ b)
  · have hnC : inC q q (.Psi κ b) = false := by
      cases e : inC q q (.Psi κ b) with
      | false => rfl
      | true => rw [(baseOf_xi_iff m q _).mpr ⟨hkx, e⟩] at hnb; cases hnb
    refine Or.inl ?_
    rcases triY hx hpF with h | e | h
    · exact h
    · exfalso
      have := inC_mono_node q q _ q (.Psi κ b) hqC
        (fun v hv _ hvp => by rw [e]; exact hvp) (fun _ _ _ h => h)
      rw [this] at hnC; cases hnC
    · exfalso
      have := inC_mono_node q q _ q (.Psi κ b) hqC
        (fun v hv _ hvp => lt_transY (hqF.of_mem_subs hv) hpF hx hvp h) (fun _ _ _ h => h)
      rw [this] at hnC; cases hnC
  · exact Or.inr (le_of_not_ltY (wnf_kTerm _) hx hkx)


/-! ### 列の不変量 -/

/-- 階 `m` 未満の項は族の閉包の列の 0 番目未満 -/
theorem lt_y0_of_lev {m : Nat} {q : Tm} {P : Option Tm} {y : Nat → Tm} (F : FamNat m q P y)
    (hm : 1 ≤ m) {x : Tm} (hx : WNF x) (hl : lev x < m) : Lt x (y 0) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hx0 : x = .zero := by
      cases x with
      | zero => rfl
      | _ => exfalso; exact absurd (lev_posY hx (by intro e; cases e)) (by omega)
    rw [hx0]
    exact zero_lt (by intro e; have := F.prin 0; rw [e] at this; cases this)
  · have h1 : Lt x (floorLev m) := by
      unfold floorLev kTerm
      rw [ite_eq_right (by omega)]
      exact lt_of_lev_lt' (by simp only [lev]; omega)
    exact lt_transY hx (wnf_kTerm _) (F.F 0) h1 F.bot

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の列が `ω` 型なら、その不変量 -/
theorem natInv_psi_succ_xi_valid {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hqX : Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → Inv u)
    (hdom : dom (.Psi (.Xi m q) X) = .omega) : NatInv (.Psi (.Xi m q) X) := by
  have hP := ht.psi
  have hρ := hP.piF
  have hρT := hP.tgt
  have hXF := hP.aF
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hX0 : X ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hpF : WNF (.Psi (.Xi m q) (predT X)) := psi_pred_wnf ht hs (fun n d e => by cases e; exact hqX)
  have hpt : Lt (.Psi (.Xi m q) (predT X)) (.Psi (.Xi m q) X) := lt_psi_psi_same.mpr (lt_predT hXF hs)
  have hpρ : Lt (.Psi (.Xi m q) (predT X)) (.Xi m q) := lt_psi_targetY hpF
  have hv : validR (.Xi m q) (pred X) = true := ltB_iff.mpr hqX
  have hcs := cs_succ_xi hXF hs hv
  have hpred : pred X = predT X := rfl
  rw [hpred] at hcs
  have hfN : ∀ n, fundNat (.Psi (.Xi m q) X) n =
      (mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).nat n := by
    intro n; rw [fundNat_psi, hcs]
  have hdom' : (mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).dom = .omega := by
    rw [← hcs, ← dom_psi]; exact hdom
  have hRinv : ∀ R, R ∈ summands q → Inv R := by
    intro R hR
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  have F := famNat_mahloVK hρ hRinv
    (fun p' hp' => by cases hp'; exact ⟨hpF, hpρ, rfl⟩)
    (fun p' hp' _ _ => by cases hp'; exact seedHyp_valid hpF)
    (fun p' hp' he => by
      cases hp'
      obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := preT (info q).sums)
        (R := lastT (info q).sums) (r := lastS (info q).sums) (P := .zero) (c := .zero)
      rw [hA] at he; cases he)
    hdom'
  obtain ⟨hk, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hpF)
  -- 列の項は `t` 未満
  have hqCt : inC q X (.Psi (.Xi m q) X) = true := by
    obtain ⟨-, hqt⟩ := (baseOf_xi_iff m q _).mp (base_selfY ht)
    exact inC_mono q q _ X _ hqt (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq
        (lt_transY hqF (predT_WNF hXF hs) hXF hqX (lt_predT hXF hs)))
  have hqXlt : Lt q X := lt_transY hqF (predT_WNF hXF hs) hXF hqX (lt_predT hXF hs)
  have hρCt : inC (.Xi m q) X (.Psi (.Xi m q) X) = true := inC_xi_iff.mpr (Or.inr ⟨hqCt, hqXlt⟩)
  have hρt : ¬ Lt (.Xi m q) (.Psi (.Xi m q) X) := Lt.asymmY ht hρ (lt_psi_targetY ht)
  have hyt : ∀ n, Lt ((mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).nat n)
      (.Psi (.Xi m q) X) := by
    intro n
    have hyC := F.ub X _ n hXF hX0 (Cut.of_wnf ht) hρCt hρt (fun p' hp' => by
      cases hp'; exact inC_of_lt_cut (Cut.of_wnf ht) _ hpF hpt)
    exact coll_psiY ht (F.F n) hyC (F.ltρ n)
  -- 共終性
  have hcof : ∀ x, WNF x → Lt x (.Psi (.Xi m q) X) →
      ∃ n, Lt x ((mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).nat n) := by
    refine cof_nat (t := .Psi (.Xi m q) X) F.F F.mono (fun x hx hxt N hN => ?_)
    have hy0 := F.seed _ rfl
    have hlev : lev x ≤ m := by have := lev_le_of_lt_gen hxt; simpa [lev] using this
    rcases Nat.lt_or_eq_of_le hlev with hl | hl
    · exact ⟨0, lt_y0_of_lev F hm hx hl⟩
    cases x with
    | zero => exfalso; simp only [lev] at hl; omega
    | M j =>
      refine ⟨0, lt_of_le_of_ltY hx (wnf_kTerm _) (F.F 0) ?_ F.bot⟩
      simp only [lev] at hl
      unfold kTerm
      rw [ite_eq_right (by have := hx.M; omega)]
      have : j = m - 1 := by omega
      rw [this]; exact Or.inl rfl
    | plus a b =>
      obtain ⟨ha, -, -, -⟩ := hx.plus
      have h1 := hN a (by simp [parL, parF]) (lt_transY ha hx ht (lt_plus_leftY hx) hxt)
      exact ⟨N, (lt_plus_prin_iffY hx (F.prin N)).mpr h1⟩
    | Om e =>
      have heF := hx.om.1
      exact F.om e N heF (hN e (by simp [parL, parF]) (lt_transY heF hx ht (lt_om_selfY hx) hxt))
    | Xi j c =>
      simp only [lev] at hl
      subst hl
      obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := .Xi j q) (γ := X) (f := c) (n := j) rfl).mp hxt
      have hxρ : Lt (.Xi j c) (.Xi j q) := lt_of_gtY hρ hx hgt
      have hne : c ≠ q := fun e => by rw [e] at hxρ; exact Lt.irrefl _ hxρ
      rcases (lt_xi_xi0 hne).mp hxρ with ⟨hcq, -⟩ | ⟨hqc, hnC⟩
      · exact F.clo c N hx hxρ hcq (fun w hw => hN w hw
          (lt_transY (hx.xi.2.1.of_mem_subs (fr_spec hw).1) hx ht (k2xY hx w hw) hxt))
      · exact ⟨0, lt_transY hx hpF (F.F 0) (xi_lt_seed_of_gt hpF hqF hx hqC hqc hnC) hy0⟩
    | Psi κ b =>
      have hQ := hx.psi
      have hκF := hQ.piF
      have hlκ : lev κ = m := by simpa [lev] using hl
      rcases triY hκF hρ with hκρ | e | hρκ
      · have h1 := tgt_lt_of_psi_lt hx ht hκρ hxt
        have h2 := hN κ (by simp [parL]) h1
        exact ⟨N, lt_transY hx hκF (F.F N) (lt_psi_targetY hx) h2⟩
      · subst e
        have hbX : Lt b X := lt_psi_psi_same.mp hxt
        refine ⟨0, lt_of_le_of_ltY hx hpF (F.F 0) ?_ hy0⟩
        rcases le_pred_of_lt_succ hXF hs hQ.aF hbX with e | h
        · rw [e]; exact Or.inl rfl
        · exact Or.inr (lt_psi_psi_same.mpr h)
      · have hxρ : Lt (.Psi κ b) (.Xi m q) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
        rcases psi_gt_lt_seed hpF hx hlκ hρκ hxρ with h | h
        · exact ⟨0, lt_transY hx hpF (F.F 0) h hy0⟩
        · exact ⟨0, lt_of_le_of_ltY hx (wnf_kTerm _) (F.F 0) h F.bot⟩
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC => ?_, fun n v hv hne hvt => ?_, fun g d n hg hg0 hd hC => ?_⟩
  · rw [hfN]; exact F.F n
  · rw [hfN]; exact hyt n
  · rw [hfN, hfN]; exact F.mono n
  · obtain ⟨n, hn⟩ := hcof x hx hxt
    exact ⟨n, by rw [hfN]; exact Or.inr hn⟩
  · rw [hfN]; intro e; have := F.prin n; rw [e] at this; cases this
  · -- 上界
    rw [hfN]
    by_cases hlt : Lt (.Psi (.Xi m q) X) d
    · exact inC_of_lt_cut hd g (F.F n) (hd _ _ (F.F n) ht (hyt n) hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, hXC, hXg⟩
    · exact absurd h1 hlt
    have hρd : ¬ Lt (.Xi m q) d := fun h' => hlt (hd _ _ ht hρ (lt_psi_targetY ht) h')
    refine F.ub g d n hg hg0 hd hρC hρd (fun p' hp' => ?_)
    cases hp'
    by_cases hpd : Lt (.Psi (.Xi m q) (predT X)) d
    · exact inC_of_lt_cut hd g hpF hpd
    · exact inC_psi_iff.mpr (Or.inr ⟨hρC, inC_of_succT (by rw [succT_predT hXF hs]; exact hXC),
        lt_transY (predT_WNF hXF hs) hXF hg (lt_predT hXF hs) hXg⟩)
  · -- 隙間
    rw [hfN]
    have h1 := gap_psi_pred ht hs (fun e => by cases e) v hv hne hvt
    exact lt_transY (ht.of_mem_subs hv) hpF (F.F n) h1
      (lt_of_lt_of_leY hpF (F.F 0) (F.F n) (F.seed _ rfl) (F.mono_le (Nat.zero_le n)))
  · rw [hfN] at hC ⊢; exact F.ub2 g d n hg hg0 hd hC

/-! ### 共終数が正則項の場合 -/

/-- 正則項 `σ` 未満の有限個の元の上に、`σ` 未満の正の項がある -/
theorem exists_above {σ : Tm} (hσF : WNF σ) (hreg : IsRegY σ) (hσ0 : Lt .zero σ) :
    ∀ l : List Tm, (∀ f, f ∈ l → WNF f ∧ Lt f σ) →
      ∃ ξ, WNF ξ ∧ Lt .zero ξ ∧ Lt ξ σ ∧ ∀ f, f ∈ l → Lt f ξ
  | [], _ => ⟨one, WNF.one, zero_lt (by intro e; cases e), one_lt_reg hσF hreg hσ0,
      fun f hf => by cases hf⟩
  | a :: l, h => by
    obtain ⟨ξ, hξ, hξ0, hξσ, hl⟩ :=
      exists_above hσF hreg hσ0 l (fun f hf => h f (List.mem_cons_of_mem _ hf))
    obtain ⟨haF, haσ⟩ := h a List.mem_cons_self
    have hμ : ∃ μ, WNF μ ∧ Lt μ σ ∧ Le a μ ∧ Le ξ μ := by
      rcases triY haF hξ with h1 | e | h1
      · exact ⟨ξ, hξ, hξσ, Or.inr h1, Or.inl rfl⟩
      · exact ⟨ξ, hξ, hξσ, Or.inl e, Or.inl rfl⟩
      · exact ⟨a, haF, haσ, Or.inl rfl, Or.inr h1⟩
    obtain ⟨μ, hμF, hμσ, haμ, hξμ⟩ := hμ
    have hsF := succT_WNF hμF
    have hμs := lt_succT μ
    refine ⟨succT μ, hsF, lt_transY WNF.zero hμF hsF (lt_of_lt_of_leY WNF.zero hξ hμF hξ0 hξμ) hμs,
      succT_lt_of_not_succ hμF hσF (not_isSucc_reg hreg) hμσ, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · exact lt_of_le_of_ltY haF hμF hsF haμ hμs
    · have hfF := (h f (List.mem_cons_of_mem _ hf)).1
      exact lt_transY hfF hμF hsF (lt_of_lt_of_leY hfF hξ hμF (hl f hf) hξμ) hμs

/-- 階 `m` 未満の項は族の閉包の列の 0 番目未満（正則項の共終数） -/
theorem lt_y0_of_lev_big {m : Nat} {q σ : Tm} {P : Option Tm} {y : Tm → Tm} (F : FamBig m q P σ y)
    (hm : 1 ≤ m) {x : Tm} (hx : WNF x) (hl : lev x < m) : Lt x (y .zero) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hx0 : x = .zero := by
      cases x with
      | zero => rfl
      | _ => exfalso; exact absurd (lev_posY hx (by intro e; cases e)) (by omega)
    rw [hx0]
    exact zero_lt (F.ne_zero .zero)
  · have h1 : Lt x (floorLev m) := by
      unfold floorLev kTerm
      rw [ite_eq_right (by omega)]
      exact lt_of_lev_lt' (by simp only [lev]; omega)
    exact lt_transY hx (wnf_kTerm _) (F.F .zero WNF.zero F.pos) h1 F.bot

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の列の共終数が正則項 `σ` なら、その不変量 -/
theorem bigInv_psi_succ_xi_valid {m : Nat} {q X σ : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hqX : Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → Inv u)
    (hdom : dom (.Psi (.Xi m q) X) = .big σ) : BigInv (.Psi (.Xi m q) X) σ := by
  have hP := ht.psi
  have hρ := hP.piF
  have hXF := hP.aF
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hX0 : X ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hX'F := predT_WNF hXF hs
  have hpF : WNF (.Psi (.Xi m q) (predT X)) := psi_pred_wnf ht hs (fun n d e => by cases e; exact hqX)
  have hpt : Lt (.Psi (.Xi m q) (predT X)) (.Psi (.Xi m q) X) := lt_psi_psi_same.mpr (lt_predT hXF hs)
  have hpρ : Lt (.Psi (.Xi m q) (predT X)) (.Xi m q) := lt_psi_targetY hpF
  have hv : validR (.Xi m q) (pred X) = true := ltB_iff.mpr hqX
  have hcs := cs_succ_xi hXF hs hv
  have hpred : pred X = predT X := rfl
  rw [hpred] at hcs
  have hfB : ∀ ξ, fundBig (.Psi (.Xi m q) X) ξ =
      (mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).big ξ := by
    intro ξ; rw [fundBig_psi, hcs]
  have hdom' : (mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))).dom = .big σ := by
    rw [← hcs, ← dom_psi]; exact hdom
  have hRinv : ∀ R, R ∈ summands q → Inv R := by
    intro R hR
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  obtain ⟨hk, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hpF)
  have hcutp := Cut.of_wnf hpF
  have hcutρ := Cut.of_wnf hρ
  -- `C(q, p)` から `C(X', p)` へ
  have hlift : ∀ w, WNF w → inC w q (.Psi (.Xi m q) (predT X)) = true →
      inC w (predT X) (.Psi (.Xi m q) (predT X)) = true := fun w hw hC =>
    inC_mono w q _ (predT X) _ hC (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hw.of_mem_subs hv) hqF hX'F hvq hqX)
  -- 加数の共終数は `p` 未満
  have F := famBig_mahloVK hρ hRinv
    (fun p' hp' => by cases hp'; exact ⟨hpF, hpρ, rfl⟩)
    (fun p' hp' _ _ => by cases hp'; exact seedHyp_valid hpF)
    (fun p' hp' he => by
      cases hp'
      obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := preT (info q).sums)
        (R := lastT (info q).sums) (r := lastS (info q).sums) (P := .zero) (c := .zero)
      rw [hA] at he; cases he)
    hdom'
  -- `σ` の位置
  have hσF := F.σF
  have hσ0 := F.pos
  have hσp : Lt σ (.Psi (.Xi m q) (predT X)) :=
    coll_psiY hpF hσF (hlift σ hσF (F.σC q _ hcutp hqC)) F.σρ
  have hσt := lt_transY hσF hpF ht hσp hpt
  have hbF := wnf_base hσF F.σreg
  have hbσ := base_lt hσF F.σreg
  have hy0F := F.F .zero WNF.zero hσ0
  have hyp : ∀ ξ, WNF ξ → Lt ξ σ →
      Lt (.Psi (.Xi m q) (predT X)) ((mahloVK m q (info q).sums (.Xi m q)
        (some (.Psi (.Xi m q) (predT X)))).big ξ) := fun ξ hξ hξσ =>
    lt_of_lt_of_leY hpF hy0F (F.F ξ hξ hξσ) (F.seed _ rfl) (F.le0 hξ hξσ)
  have hσy : ∀ ξ, WNF ξ → Lt ξ σ → Lt σ ((mahloVK m q (info q).sums (.Xi m q)
      (some (.Psi (.Xi m q) (predT X)))).big ξ) := fun ξ hξ hξσ =>
    lt_transY hσF hpF (F.F ξ hξ hξσ) hσp (hyp ξ hξ hξσ)
  -- 列の項は `t` 未満
  have hqCt : inC q X (.Psi (.Xi m q) X) = true := by
    obtain ⟨-, hqt⟩ := (baseOf_xi_iff m q _).mp (base_selfY ht)
    exact inC_mono q q _ X _ hqt (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq
        (lt_transY hqF hX'F hXF hqX (lt_predT hXF hs)))
  have hqXlt : Lt q X := lt_transY hqF hX'F hXF hqX (lt_predT hXF hs)
  have hρCt : inC (.Xi m q) X (.Psi (.Xi m q) X) = true := inC_xi_iff.mpr (Or.inr ⟨hqCt, hqXlt⟩)
  have hρt : ¬ Lt (.Xi m q) (.Psi (.Xi m q) X) := Lt.asymmY ht hρ (lt_psi_targetY ht)
  have hcutt := Cut.of_wnf ht
  have hyt : ∀ ξ, WNF ξ → Lt ξ σ → Lt ((mahloVK m q (info q).sums (.Xi m q)
      (some (.Psi (.Xi m q) (predT X)))).big ξ) (.Psi (.Xi m q) X) := by
    intro ξ hξ hξσ
    have hyC := F.ub X _ ξ hXF hX0 hcutt hξ hξσ
      (inC_of_lt_cut hcutt _ hbF (lt_transY hbF hσF ht hbσ hσt)) hρCt hρt
      (fun p' hp' => by cases hp'; exact inC_of_lt_cut hcutt _ hpF hpt)
      (inC_of_lt_cut hcutt _ hξ (lt_transY hξ hσF ht hξσ hσt))
    exact coll_psiY ht (F.F ξ hξ hξσ) hyC (F.ltρ ξ hξ hξσ)
  -- 添字での共終性
  have hcloS : ∀ ξ, WNF ξ → Lt .zero ξ → Lt ξ σ → ∀ x, WNF x → Lt x (.Psi (.Xi m q) X) →
      (∀ f, f ∈ lfr σ x → Lt f ξ) → Lt x ((mahloVK m q (info q).sums (.Xi m q)
        (some (.Psi (.Xi m q) (predT X)))).big ξ) := by
    intro ξ hξ hξ0 hξσ x
    induction x using size_induction with
    | h x ih' =>
    intro hx hxt hfr
    have hyξ := F.F ξ hξ hξσ
    have hy0ξ := F.le0 hξ hξσ
    by_cases hxσ : Lt x σ
    · have h1 := hfr x (by rw [lfr_of_lt hxσ]; exact List.mem_singleton.mpr rfl)
      exact lt_transY hx hξ hyξ h1 (F.ge ξ hξ hξσ)
    have hpart : ∀ w, w ∈ parF x → Lt w ((mahloVK m q (info q).sums (.Xi m q)
        (some (.Psi (.Xi m q) (predT X)))).big ξ) := fun w hw => by
      have hwx := parF_lt hx hw
      have hwF := hx.of_mem_subs (parF_mem_subs hw)
      refine ih' w (parL_sub (parF_sub_parL hw)).2 hwF (lt_transY hwF hx ht hwx hxt) (fun f hf => ?_)
      obtain ⟨g, hg, hfg⟩ := lfr_of_parF hσF hx hxσ hw hf
      exact lt_of_le_of_ltY (hwF.of_mem_subs (lfr_spec hf).1) (hx.of_mem_subs (lfr_spec hg).1)
        hξ hfg (hfr g hg)
    have hlev : lev x ≤ m := by have := lev_le_of_lt_gen hxt; simpa [lev] using this
    rcases Nat.lt_or_eq_of_le hlev with hl | hl
    · exact lt_of_lt_of_leY hx hy0F hyξ (lt_y0_of_lev_big F hm hx hl) hy0ξ
    cases x with
    | zero => exfalso; simp only [lev] at hl; omega
    | M j =>
      refine lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (wnf_kTerm _) hy0F ?_ F.bot) hy0ξ
      simp only [lev] at hl
      unfold kTerm
      rw [ite_eq_right (by have := hx.M; omega)]
      have : j = m - 1 := by omega
      rw [this]; exact Or.inl rfl
    | plus a b => exact (lt_plus_prin_iffY hx (F.prin ξ)).mpr (hpart a (by simp [parF]))
    | Om e => exact (lt_om_OFG (F.OF ξ) hyξ).mpr (hpart e (by simp [parF]))
    | Xi j c =>
      simp only [lev] at hl
      subst hl
      obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := .Xi j q) (γ := X) (f := c) (n := j) rfl).mp hxt
      have hxρ : Lt (.Xi j c) (.Xi j q) := lt_of_gtY hρ hx hgt
      have hne : c ≠ q := fun e => by rw [e] at hxρ; exact Lt.irrefl _ hxρ
      rcases (lt_xi_xi0 hne).mp hxρ with ⟨hcq, -⟩ | ⟨hqc, hnC⟩
      · exact F.clo c ξ hx hxρ hcq hξ hξ0 hξσ (fun f hf => hfr f ((mem_lfr_xi hxσ).mpr hf))
          (fun w hw => hpart w hw)
      · exact lt_transY hx hpF hyξ (xi_lt_seed_of_gt hpF hqF hx hqC hqc hnC) (hyp ξ hξ hξσ)
    | Psi κ b =>
      have hQ := hx.psi
      have hκF := hQ.piF
      have hlκ : lev κ = m := by simpa [lev] using hl
      rcases triY hκF hρ with hκρ | e | hρκ
      · have h1 := tgt_lt_of_psi_lt hx ht hκρ hxt
        have h2 := ih' κ (by simp only [Tm.size]; omega) hκF h1
          (fun f hf => hfr f ((mem_lfr_psi hxσ).mpr (Or.inl hf)))
        exact lt_transY hx hκF hyξ (lt_psi_targetY hx) h2
      · subst e
        have hbX : Lt b X := lt_psi_psi_same.mp hxt
        refine lt_of_le_of_ltY hx hpF hyξ ?_ (hyp ξ hξ hξσ)
        rcases le_pred_of_lt_succ hXF hs hQ.aF hbX with e | h
        · rw [e]; exact Or.inl rfl
        · exact Or.inr (lt_psi_psi_same.mpr h)
      · have hxρ : Lt (.Psi κ b) (.Xi m q) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
        rcases psi_gt_lt_seed hpF hx hlκ hρκ hxρ with h | h
        · exact lt_transY hx hpF hyξ h (hyp ξ hξ hξσ)
        · exact lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (wnf_kTerm _) hy0F h F.bot) hy0ξ
  -- 隙間
  have hgapS : ∀ ξ, WNF ξ → Lt ξ σ → ∀ v, v ∈ subs (Tm.Psi (.Xi m q) X) → v ≠ .Psi (.Xi m q) X →
      Lt v (.Psi (.Xi m q) X) → Lt v ((mahloVK m q (info q).sums (.Xi m q)
        (some (.Psi (.Xi m q) (predT X)))).big ξ) := by
    intro ξ hξ hξσ v hv hne hvt
    have h1 := gap_psi_pred ht hs (fun e => by cases e) v hv hne hvt
    exact lt_transY (ht.of_mem_subs hv) hpF (F.F ξ hξ hξσ) h1 (hyp ξ hξ hξσ)
  refine {
    props := ⟨hσF, hσ0, fun ξ hξ hξσ => ?_, fun ξ hξ hξσ => ?_,
      fun ξ η hξ hη hξη hησ => ?_, fun x hx hxt => ?_⟩
    σreg := F.σreg
    σsub := subs_psi_p (subs_xi F.σsub)
    σle := Or.inr hσt
    pos := fun ξ hξ hξσ h0 => by rw [hfB] at h0; exact absurd h0 (F.ne_zero ξ)
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => by rw [hfB] at hC; exact F.lo g d ξ hd hξ hξσ hC
    ge := fun ξ hξ hξσ => by rw [hfB]; exact Or.inr (F.ge ξ hξ hξσ)
    gap := fun ξ v hξ hξσ hv hne hvt => by rw [hfB]; exact Or.inr (hgapS ξ hξ hξσ v hv hne hvt)
    gapP := fun _ ξ v hξ hξσ hv hne hvt => by rw [hfB]; exact hgapS ξ hξ hξσ v hv hne hvt
    lclo := fun x ξ hx hxt hξ hξ0 hξσ hfr => by rw [hfB]; exact hcloS ξ hξ hξ0 hξσ x hx hxt hfr
    nsucc := fun ξ hξ hξσ _ _ => by
      rw [hfB]
      obtain ⟨A, hA⟩ := F.xi ξ
      rw [hA]; simp [isSucc, summands, one]
    bge := fun ξ hξ hξσ => by rw [hfB]; exact Or.inr (F.blt ξ hξ hξσ)
    lbK := fun m' e _ ξ hξ hξσ => by rw [hfB, ← e]; exact Or.inr (hσy ξ hξ hξσ)
    lbS := fun m' e _ ξ hξ hξσ => by
      rw [hfB]
      have hm' : 1 ≤ m' := by have h := hσF; rw [e] at h; exact h.M
      have hSF := WNF.succM hm'
      refine Or.inr ((lt_om_OFG (F.OF ξ) (F.F ξ hξ hξσ)).mpr
        ((lt_plus_prin_iffY hSF.om.1 (F.prin ξ)).mpr ?_))
      rw [← e]; exact hσy ξ hξ hξσ
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      rw [hfB] at hC ⊢; exact F.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [hfB] at hC; exact F.bw g d ξ L hd hξ hξσ hL hσL hC }
  · rw [hfB]; exact F.F ξ hξ hξσ
  · rw [hfB]; exact hyt ξ hξ hξσ
  · rw [hfB, hfB]; exact F.mono ξ η hξ hη hξη hησ
  · obtain ⟨ξ, hξ, hξ0, hξσ, hl⟩ := exists_above hσF F.σreg hσ0 (lfr σ x)
      (fun f hf => ⟨hx.of_mem_subs (lfr_spec hf).1, (lfr_spec hf).2⟩)
    exact ⟨ξ, hξ, hξσ, by rw [hfB]; exact Or.inr (hcloS ξ hξ hξ0 hξσ x hx hxt hl)⟩
  · by_cases hlt : Lt (.Psi (.Xi m q) X) d
    · exact inC_of_lt_cut hd g hσF (hd _ _ hσF ht hσt hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, -, -⟩
    · exact absurd h1 hlt
    rcases inC_xi_iff.mp hρC with h2 | ⟨hqC', -⟩
    · exact inC_of_lt_cut hd g hσF (hd _ _ hσF hρ F.σρ h2)
    · exact F.σC g d hd hqC'
  · rw [hfB]
    by_cases hlt : Lt (.Psi (.Xi m q) X) d
    · exact inC_of_lt_cut hd g (F.F ξ hξ hξσ) (hd _ _ (F.F ξ hξ hξσ) ht (hyt ξ hξ hξσ) hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, hXC, hXg⟩
    · exact absurd h1 hlt
    have hρd : ¬ Lt (.Xi m q) d := fun h' => hlt (hd _ _ ht hρ (lt_psi_targetY ht) h')
    refine F.ub g d ξ hg hg0 hd hξ hξσ hbC hρC hρd (fun p' hp' => ?_) hξC
    cases hp'
    by_cases hpd : Lt (.Psi (.Xi m q) (predT X)) d
    · exact inC_of_lt_cut hd g hpF hpd
    · exact inC_psi_iff.mpr (Or.inr ⟨hρC, inC_of_succT (by rw [succT_predT hXF hs]; exact hXC),
        lt_transY hX'F hXF hg (lt_predT hXF hs) hXg⟩)

/-! ### まとめ -/

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の列の不変量 -/
theorem inv_psi_succ_xi_valid {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hqX : Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → Inv u) : Inv (.Psi (.Xi m q) X) :=
  ⟨fun hd => natInv_psi_succ_xi_valid ht hs hqX ih hd,
    fun _ hd => bigInv_psi_succ_xi_valid ht hs hqX ih hd⟩

/-- `Ξ` への崩壊の後者のうち残りの場合：底 `X' ≤ q` -/
def PsiXiSuccFloor : Prop :=
  ∀ n p X, WNF (.Psi (.Xi n p) X) → isSucc X = true → ¬ Lt p (predT X) →
    (∀ u, u.size < (Tm.Psi (.Xi n p) X).size → WNF u → Inv u) → Inv (.Psi (.Xi n p) X)

theorem psiXiSuccRest_of (hF : PsiXiSuccFloor) : PsiXiSuccRest := by
  intro n p X ht hs _ ih
  by_cases h : Lt p (predT X)
  · exact inv_psi_succ_xi_valid ht hs h ih
  · exact hF n p X ht hs h ih

end MahloOCF.FS
