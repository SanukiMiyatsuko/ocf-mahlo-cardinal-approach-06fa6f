import Mahlo.FS.PsiKO

/-! 目標の族 `Ξ_m(q)` の閉包の近似 `Ξ_m(pre ⊕ (P # x))` の基本的な性質。

`q` の加数を `pre ++ R :: rest` と分け、`T = pre ⊕ R` を `q` の先頭部分とする。

* 大きさの議論（`lt_T_of_sub`）：`pre ++ [R]` の加数の真の部分項で `q` 未満のものは `T` 未満
  （`T` 以上なら加数の並びが `pre ++ [R]` で始まり、元の加数を部分項に含んでしまう）。
  これで `q` の加数の `C(q, D)` への所属は段 `pre ⊕ A'` に移る（`inC_prefix`）。
* 近似 `Ξ_m(pre ⊕ (P # x))`（`x = R[ν]`）は標準形で（`XG.nf`）、`Ξ_m(q)` 未満（`XG.ltρ`）、`x` について単調
  （`XG.lt2`）、種 `P` より大きい（`XG.seed_lt`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 先頭部分 -/

/-- 加数の並びの比較：`pre ++ [R] ≤ l < pre ++ R :: rest` なら `l` は `pre ++ [R]` で始まる -/
theorem prefix_of_between : ∀ (pre : List Tm) (R : Tm) (rest l : List Tm),
    (∀ x, x ∈ pre ++ R :: rest → WNF x ∧ isPrincipal x = true) →
    (∀ x, x ∈ l → WNF x ∧ isPrincipal x = true) →
    cmpList l (pre ++ [R]) ≠ .lt → cmpList l (pre ++ R :: rest) = .lt →
    ∃ l', l = pre ++ R :: l'
  | [], R, _, [], _, _, h1, _ => absurd (cmpList_nil_cons R []) h1
  | [], R, rest, a :: l', hq, hl, h1, h2 => by
    have hR := hq R (by simp)
    have ha := hl a List.mem_cons_self
    rcases hc : cmpP a R with _ | _ | _
    · rw [List.nil_append, cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at h1
      exact absurd rfl h1
    · exact ⟨l', by rw [eq_of_cmpP_eqY ha.1 hR.1 ha.2 hR.2 hc]; rfl⟩
    · rw [List.nil_append, cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at h2
      cases h2
  | b :: _, _, _, [], _, _, h1, _ => absurd (cmpList_nil_cons b _) h1
  | b :: pre', R, rest, a :: l', hq, hl, h1, h2 => by
    have hb := hq b List.mem_cons_self
    have ha := hl a List.mem_cons_self
    rcases hc : cmpP a b with _ | _ | _
    · rw [List.cons_append, cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at h1
      exact absurd rfl h1
    · have e := eq_of_cmpP_eqY ha.1 hb.1 ha.2 hb.2 hc
      subst e
      rw [List.cons_append, cmpList_cons_cons_eq _ _ hc] at h1 h2
      obtain ⟨l'', hl''⟩ := prefix_of_between pre' R rest l' (fun x hx => hq x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h1 h2
      exact ⟨l'', by rw [hl'']; rfl⟩
    · rw [List.cons_append, cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at h2
      cases h2

theorem nfl_prefix {pre rest : List Tm} {R : Tm} (h : NFL (pre ++ R :: rest)) : NFL (pre ++ [R]) := by
  have e : pre ++ R :: rest = (pre ++ [R]) ++ rest := by simp
  rw [e] at h
  exact nfl_append_left h

/-- 大きさの議論：`q` の加数 `pre ++ R :: rest` のうち `s ∈ pre ++ [R]` の真の部分項 `v` が `q` 未満なら
    `v < T = pre ⊕ R` -/
theorem lt_T_of_sub {q R s v : Tm} {pre rest : List Tm} (hq : WNF q)
    (hsq : summands q = pre ++ R :: rest) (hs : s ∈ pre ++ [R]) (hv : v ∈ subs s) (hne : v ≠ s)
    (hvF : WNF v) (hvq : Lt v q) : Lt v (ofSummands (pre ++ [R])) := by
  have hN : NFL (pre ++ R :: rest) := by rw [← hsq]; exact nfl_summands hq
  have hT := nfl_prefix hN
  have hsT : summands (ofSummands (pre ++ [R])) = pre ++ [R] :=
    summands_ofSummands _ (nfl_principal hT)
  by_cases hlt : Lt v (ofSummands (pre ++ [R]))
  · exact hlt
  exfalso
  have h1 : cmpList (summands v) (pre ++ [R]) ≠ .lt := by
    intro h; apply hlt; unfold Lt; rw [cmp_eq, hsT]; exact h
  have h2 : cmpList (summands v) (pre ++ R :: rest) = .lt := by
    have := hvq; unfold Lt at this; rw [cmp_eq, hsq] at this; exact this
  obtain ⟨l', hl'⟩ := prefix_of_between pre R rest (summands v) hN.1 (nfl_summands hvF).1 h1 h2
  have hsv : s ∈ summands v := by
    rw [hl']
    rcases List.mem_append.mp hs with h | h
    · exact List.mem_append_left _ h
    · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ List.mem_cons_self
  exact hne (eq_of_mem_subs_size hv (size_le_of_mem_subs (mem_subs_of_mem_summands hsv)))

/-- `q` の加数 `s ∈ pre ++ [R]` の `C(q, D)` への所属は段 `pre ⊕ A'` に移る（`A'` は `R` の隙間を満たす） -/
theorem inC_prefix {q R s A' D : Tm} {pre rest : List Tm} (hq : WNF q)
    (hsq : summands q = pre ++ R :: rest) (hA : WNF A')
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v A')
    (hpos : A' = .zero → ∀ v, v ∈ subs R → v = R)
    (hs : s ∈ pre ++ [R]) (hC : inC s q D = true) : inC s (oadd (ofSummands pre) A') D = true := by
  have hN : NFL (pre ++ R :: rest) := by rw [← hsq]; exact nfl_summands hq
  have hT := nfl_prefix hN
  have hTF : WNF (ofSummands (pre ++ [R])) := wnf_ofSummands hT
  have hsT : summands (ofSummands (pre ++ [R])) = pre ++ [R] :=
    summands_ofSummands _ (nfl_principal hT)
  have hArg := argCond hTF hsT hA hgap hpos
  have hsT' : s ∈ summands (ofSummands (pre ++ [R])) := by rw [hsT]; exact hs
  have hsF : WNF s := (hT.1 s hs).1
  exact inC_mono_node s q D _ D hC (fun _ _ _ h => h) (fun v hv hvs hvq =>
    hArg s hsT' v hv (ne_of_size_lt hvs)
      (lt_T_of_sub hq hsq hs hv (ne_of_size_lt hvs) (hsF.of_mem_subs hv) hvq))

/-! ### 近似 `Ξ_m(pre ⊕ (P # x))` -/

/-- `Ξ` の族の近似の引数 `pre ⊕ (P # x)` -/
@[reducible] def xa (pre : List Tm) (P x : Tm) : Tm := oadd (ofSummands pre) (nsum P x)

/-- `Ξ_m(A)` の引数の加数で `M_m` 未満のものは `Ξ_m(A)` 未満 -/
theorem summand_lt_xi {m : Nat} {A u : Tm} (hy : WNF (.Xi m A)) (hu : u ∈ summands A)
    (huM : Lt u (.M m)) : Lt u (.Xi m A) := by
  have hA := hy.xi.2.1
  exact coll_xi0 hy u (summands_WNF _ hA u hu).1 (inC_of_mem_summands hA (xi_selfY hy) hu) huM

theorem combine_xi (m : Nat) (pre : List Tm) {P x : Tm} (hP : WNF P) (hx : WNF x) :
    combine (.xi m) pre .zero P x = xa pre P x := by
  simp only [combine, xa]
  rw [zero_nsum _ (wnf_nsum hP hx)]

/-- `Ξ_m(q)` の加数 `R` での近似の仮定：`summands q = pre ++ R :: rest`、種 `P`（`P < R`、`P < M_m`、
    `0` か主要項） -/
structure XG (m : Nat) (q P : Tm) (pre rest : List Tm) (R : Tm) : Prop where
  ht : WNF (.Xi m q)
  hsum : summands q = pre ++ R :: rest
  hPF : WNF P
  hPR : Lt P R
  hPM : Lt P (.M m)
  hPp : P = .zero ∨ isPrincipal P = true

namespace XG

variable {m : Nat} {q P : Tm} {pre rest : List Tm} {R : Tm}

theorem hm (G : XG m q P pre rest R) : 1 ≤ m := G.ht.xi.1
theorem hqF (G : XG m q P pre rest R) : WNF q := G.ht.xi.2.1
theorem hqC (G : XG m q P pre rest R) : inC q q (.M m) = true := G.ht.xi.2.2.2
theorem hMF (G : XG m q P pre rest R) : WNF (.M m) := WNF.M' G.hm
theorem hN (G : XG m q P pre rest R) : NFL (pre ++ R :: rest) := G.hsum ▸ nfl_summands G.hqF
theorem hNT (G : XG m q P pre rest R) : NFL (pre ++ [R]) := nfl_prefix G.hN
theorem hRF (G : XG m q P pre rest R) : WNF R := (G.hNT.1 R (by simp)).1
theorem hRp (G : XG m q P pre rest R) : isPrincipal R = true := (G.hNT.1 R (by simp)).2
theorem hR0 (G : XG m q P pre rest R) : R ≠ .zero := by
  intro e; have := G.hRp; rw [e] at this; cases this
theorem hpreF (G : XG m q P pre rest R) : WNF (ofSummands pre) := wnf_ofSummands (nfl_append_left G.hNT)
theorem hTF (G : XG m q P pre rest R) : WNF (ofSummands (pre ++ [R])) := wnf_ofSummands G.hNT
theorem hsT (G : XG m q P pre rest R) : summands (ofSummands (pre ++ [R])) = pre ++ [R] :=
  summands_ofSummands _ (nfl_principal G.hNT)
theorem hTe (G : XG m q P pre rest R) : ofSummands (pre ++ [R]) = oadd (ofSummands pre) R :=
  eq_oadd_of_summands G.hTF G.hsT
theorem hRq (G : XG m q P pre rest R) : R ∈ summands q := by
  rw [G.hsum]; exact List.mem_append_right _ List.mem_cons_self
theorem hpreq (G : XG m q P pre rest R) {s : Tm} (hs : s ∈ pre) : s ∈ summands q := by
  rw [G.hsum]; exact List.mem_append_left _ hs
theorem hTq (G : XG m q P pre rest R) : Le (ofSummands (pre ++ [R])) q := by
  refine le_of_ne_gtY G.hTF G.hqF ?_
  rw [cmp_eq, G.hsT, G.hsum]
  have e : pre ++ R :: rest = (pre ++ [R]) ++ rest := by simp
  rw [e]
  have h := cmpList_take_ne_gt ((pre ++ [R]) ++ rest) (pre ++ [R]).length
  rwa [List.take_left] at h

theorem hyF (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) : WNF (nsum P x) := wnf_nsum G.hPF hx
theorem hyR (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) : Lt (nsum P x) R :=
  nsum_lt_prin G.hPF hx G.hRp G.hPR hxR
theorem hAF (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) : WNF (xa pre P x) :=
  wnf_oadd G.hpreF (G.hyF hx)
theorem hAT (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) :
    Lt (xa pre P x) (ofSummands (pre ++ [R])) := by
  rw [G.hTe]; exact oadd_lt_oadd G.hpreF (G.hyF hx) G.hRF (G.hyR hx hxR)
theorem hAq (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) : Lt (xa pre P x) q :=
  lt_of_lt_of_leY (G.hAF hx) G.hTF G.hqF (G.hAT hx hxR) G.hTq
theorem hxA (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) : Le x (xa pre P x) :=
  le_transY hx (G.hyF hx) (G.hAF hx) (le_nsum_right G.hPF hx) (le_oadd_right G.hpreF (G.hyF hx))
theorem hPA (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) : Le P (xa pre P x) :=
  le_transY G.hPF (G.hyF hx) (G.hAF hx) (le_nsum_left G.hPF hx) (le_oadd_right G.hpreF (G.hyF hx))
theorem hAmono (G : XG m q P pre rest R) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (h : Lt x x') :
    Lt (xa pre P x) (xa pre P x') :=
  oadd_lt_oadd G.hpreF (G.hyF hx) (G.hyF hx') (nsum_lt_right G.hPF hx hx' h)

/-- 近似の引数の加数 -/
theorem summands_xa (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) :
    summands (xa pre P x) = pre ++ summands (nsum P x) := by
  have hy := G.hyF hx
  have hyR := G.hyR hx hxR
  have hn : NFL (pre ++ summands (nsum P x)) := by
    refine nfl_append (nfl_append_left G.hNT) (nfl_summands hy) (fun a b ha hb => ?_)
    have haR : cmp R a ≠ .gt := by
      have h := nfl_append_ge G.hNT a (List.mem_of_getLast? ha) R (by simp)
      exact h
    have hbF := (summands_WNF _ hy b (List.mem_of_mem_head? hb)).1
    have hby : Le b (nsum P x) := le_of_mem_summands hy (List.mem_of_mem_head? hb)
    have hbR : Lt b R := lt_of_le_of_ltY hbF hy G.hRF hby hyR
    have haF := (G.hNT.1 a (List.mem_append_left _ (List.mem_of_getLast? ha))).1
    exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hbF G.hRF haF hbR (le_of_ne_gtY G.hRF haF haR)))
  have h := summands_oadd_nfl hn
  rw [ofSummands_summands _ hy] at h
  exact h

theorem mem_xa_P (G : XG m q P pre rest R) {x u : Tm} (hx : WNF x) (hxR : Lt x R)
    (hu : u ∈ summands P) : u ∈ summands (xa pre P x) := by
  rw [G.summands_xa hx hxR]
  refine List.mem_append_right _ ?_
  rw [nsum_comm G.hPF hx]
  exact mem_summands_nsum_right hx G.hPF hu

theorem mem_xa_x (G : XG m q P pre rest R) {x u : Tm} (hx : WNF x) (hxR : Lt x R)
    (hu : u ∈ summands x) : u ∈ summands (xa pre P x) := by
  rw [G.summands_xa hx hxR]
  exact List.mem_append_right _ (mem_summands_nsum_right G.hPF hx hu)

theorem mem_xa_pre (G : XG m q P pre rest R) {x u : Tm} (hx : WNF x) (hxR : Lt x R)
    (hu : u ∈ pre) : u ∈ summands (xa pre P x) := by
  rw [G.summands_xa hx hxR]; exact List.mem_append_left _ hu

/-- 近似の引数の所属 -/
theorem inC_A (G : XG m q P pre rest R) {x g d : Tm} (hx : WNF x)
    (hpre : ∀ s, s ∈ pre → inC s g d = true) (hP : inC P g d = true) (hxC : inC x g d = true) :
    inC (xa pre P x) g d = true :=
  inC_oadd G.hpreF (G.hyF hx) ((inC_ofSummands pre).mpr hpre) (inC_nsum G.hPF hx hP hxC)

/-- 近似の引数の成分 -/
theorem parts (G : XG m q P pre rest R) {x g d : Tm} (hx : WNF x) (hxR : Lt x R)
    (h : inC (xa pre P x) g d = true) :
    (∀ s, s ∈ pre → inC s g d = true) ∧ inC P g d = true ∧ inC x g d = true := by
  have hA := G.hAF hx
  refine ⟨fun s hs => inC_of_mem_summands hA h (G.mem_xa_pre hx hxR hs), ?_, ?_⟩
  · exact (inC_iff_summandsW G.hPF).mpr (fun u hu => inC_of_mem_summands hA h (G.mem_xa_P hx hxR hu))
  · exact (inC_iff_summandsW hx).mpr (fun u hu => inC_of_mem_summands hA h (G.mem_xa_x hx hxR hu))

/-- `pre` の加数は段 `pre ⊕ (P # x)` で `C(·, D)` に入る（`q ∈ C(q, D)` から） -/
theorem pre_inC (G : XG m q P pre rest R) {x D : Tm} (hx : WNF x)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hpos : x = .zero → ∀ v, v ∈ subs R → v = R) (hqD : inC q q D = true) :
    ∀ s, s ∈ pre ++ [R] → inC s (xa pre P x) D = true := by
  have hy := G.hyF hx
  intro s hs
  have hsq : s ∈ summands q := by
    rw [G.hsum]
    rcases List.mem_append.mp hs with h | h
    · exact List.mem_append_left _ h
    · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ List.mem_cons_self
  exact inC_prefix G.hqF G.hsum hy
    (fun v hv hne hlt => lt_of_lt_of_leY (G.hRF.of_mem_subs hv) hx hy (hgap v hv hne hlt)
      (le_nsum_right G.hPF hx))
    (fun h0 => hpos (by
      have h1 := le_nsum_right G.hPF hx
      rw [h0] at h1
      rcases h1 with e | e
      · exact e
      · exact absurd e (not_lt_zero _)))
    hs (inC_of_mem_summands G.hqF hqD hsq)

/-- 標準形 -/
theorem nf (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hpos : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hxC : inC x (xa pre P x) (.M m) = true) : WNF (.Xi m (xa pre P x)) := by
  have hA := G.hAF hx
  have hle : Le (xa pre P x) (succM m) :=
    le_transY hA G.hqF (WNF.succM G.hm) (Or.inr (G.hAq hx hxR))
      (le_of_ne_gtY G.hqF (WNF.succM G.hm) G.ht.xi.2.2.1)
  refine WNF.mk_xi G.hm hA (ne_gt_of_le hle) (G.inC_A hx (fun s hs => ?_)
    (inC_of_lt_cut (Cut.of_wnf G.hMF) _ G.hPF G.hPM) hxC)
  exact G.pre_inC hx hgap hpos G.hqC s (List.mem_append_left _ hs)

/-- `pre` の加数は `C(q, Ξ_m(q))` に入る -/
theorem pre_inCρ (G : XG m q P pre rest R) : ∀ s, s ∈ pre ++ [R] → inC s q (.Xi m q) = true := by
  intro s hs
  refine inC_of_mem_summands G.hqF (xi_selfY G.ht) ?_
  rw [G.hsum]
  rcases List.mem_append.mp hs with h | h
  · exact List.mem_append_left _ h
  · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ List.mem_cons_self

/-- 崩壊の性質：近似は `Ξ_m(q)` 未満 -/
theorem ltρ (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hxC : inC x q (.Xi m q) = true) (hPC : inC P q (.Xi m q) = true) :
    Lt (.Xi m (xa pre P x)) (.Xi m q) := by
  have hAq := G.hAq hx hxR
  exact (lt_xi_xi0 (Lt.ne hAq)).mpr (Or.inl ⟨hAq, G.inC_A hx
    (fun s hs => G.pre_inCρ s (List.mem_append_left _ hs)) hPC hxC⟩)

/-- 種は近似未満 -/
theorem seed_lt (G : XG m q P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hy : WNF (.Xi m (xa pre P x))) : Lt P (.Xi m (xa pre P x)) := by
  rcases G.hPp with h0 | hp
  · rw [h0]; exact zero_lt (by intro e; cases e)
  · exact summand_lt_xi hy (G.mem_xa_P hx hxR (by rw [summands_principal hp]; exact List.mem_singleton.mpr rfl))
      G.hPM

/-- 2 点の比較 -/
theorem lt2 (G : XG m q P pre rest R) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (hx'R : Lt x' R)
    (hxx : Lt x x') (hy' : WNF (.Xi m (xa pre P x')))
    (hxC : inC x (xa pre P x') (.Xi m (xa pre P x')) = true) :
    Lt (.Xi m (xa pre P x)) (.Xi m (xa pre P x')) := by
  have hAA := G.hAmono hx hx' hxx
  obtain ⟨h1, h2, -⟩ := G.parts hx' hx'R (xi_selfY hy')
  exact (lt_xi_xi0 (Lt.ne hAA)).mpr (Or.inl ⟨hAA, G.inC_A hx h1 h2 hxC⟩)

end XG

end MahloOCF.FS
