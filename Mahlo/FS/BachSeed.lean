import Mahlo.FS.BachFam

/-! 種つきの近似 `Ξ_m(H ⊕ P')`（`H` の加数は全て `M_m` 以上、種 `P' < M_m` は主要項）の梯子。

区間の `E ∈ (H ⊕ P', H' ⊕ P']` で `Ξ_m(H ⊕ P') < Ξ_m(E)`・前線が全て `Ξ_m(H ⊕ P')` 未満のものは、

* `E[0] ≥ H ⊕ P'` で関連する（`P' < Ξ_m(E[0])`）なら `F = E[0]`（`Ξ_m(E[0]) ≤ base[0]`）。
* そうでなければ `Ξ_m(E[0]) ≤ P'` で、`E` の前線の最大元 `p ≥ P'` は素の近似の 0 番目を越え、底の閉包は
  種 `p` の近似：その 0 番目 `Ξ_m(A₀)` の引数は `H` 以上で、`H ≤ A₀ < H ⊕ P'` なら `Ξ_m(A₀) < P'`（種の閉性）
  なので `A₀ ≥ H ⊕ P'`。 -/

namespace MahloOCF.FS

open Tm

/-! ### 和の分解 -/

/-- 加数の並びの連結は和 -/
theorem ofSummands_append {L S : List Tm} (h : NFL (L ++ S)) :
    ofSummands (L ++ S) = oadd (ofSummands L) (ofSummands S) := by
  have hL := nfl_append_left h
  have hS := nfl_append_right h
  have hw : WNF (oadd (ofSummands L) (ofSummands S)) := wnf_oadd (wnf_ofSummands hL) (wnf_ofSummands hS)
  rw [← summands_oadd_nfl h, ofSummands_summands _ hw]

/-- `H ≤ Z < H ⊕ Q`（`Q` は主要項、`H` の加数は全て `Q` 以上）なら `Z = H ⊕ w`（`w < Q`） -/
theorem between_oadd {H Z Q : Tm} (hH : WNF H) (hZ : WNF Z) (hQF : WNF Q) (hQp : isPrincipal Q = true)
    (hN : NFL (summands H ++ [Q])) (h1 : Le H Z) (h2 : Lt Z (oadd H Q)) :
    ∃ w, Z = oadd H w ∧ WNF w ∧ Lt w Q ∧ NFL (summands H ++ summands w) := by
  by_cases hH0 : H = .zero
  · subst hH0
    rw [zero_oadd hQF] at h2
    exact ⟨Z, (zero_oadd hZ).symm, hZ, h2, by simpa [summands] using nfl_summands hZ⟩
  have hne := summands_ne_nil hH0
  obtain ⟨pre, R, hpr⟩ : ∃ pre R, summands H = pre ++ [R] :=
    ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
  have hHe : H = ofSummands (pre ++ [R]) := by rw [← hpr, ofSummands_summands _ hH]
  have hN' : NFL ((pre ++ [R]) ++ [Q]) := by rw [← hpr]; exact hN
  have hsHQ : summands (oadd H Q) = pre ++ R :: [Q] := by
    have := summands_oadd_nfl hN'
    rw [← hHe] at this
    rw [show (ofSummands [Q]) = Q from rfl] at this
    rw [this]; simp
  have hZs := nfl_summands hZ
  have h1' : cmpList (summands Z) (pre ++ [R]) ≠ .lt := by
    intro h
    apply not_lt_of_leY hH hZ h1
    unfold Lt; rw [cmp_eq, hpr]; exact h
  have h2' : cmpList (summands Z) (pre ++ R :: [Q]) = .lt := by
    have := h2; unfold Lt at this; rw [cmp_eq, hsHQ] at this; exact this
  have hq : ∀ x, x ∈ pre ++ R :: [Q] → WNF x ∧ isPrincipal x = true := by
    intro x hx
    have : x ∈ (pre ++ [R]) ++ [Q] := by simpa using hx
    exact hN'.1 x this
  obtain ⟨l', hl'⟩ := prefix_of_between pre R [Q] (summands Z) hq hZs.1 h1' h2'
  have hZl : summands Z = (pre ++ [R]) ++ l' := by rw [hl']; simp
  have hNZ : NFL ((pre ++ [R]) ++ l') := by rw [← hZl]; exact hZs
  have hl'N : NFL l' := nfl_append_right hNZ
  refine ⟨ofSummands l', ?_, wnf_ofSummands hl'N, ?_, ?_⟩
  · rw [← ofSummands_summands Z hZ, hZl, ofSummands_append hNZ, ← hHe]
  · unfold Lt
    rw [cmp_eq, summands_ofSummands l' (nfl_principal hl'N), summands_principal hQp]
    have := h2'
    rw [hl', show pre ++ R :: l' = (pre ++ [R]) ++ l' by simp,
      show pre ++ R :: [Q] = (pre ++ [R]) ++ [Q] by simp, cmpList_append_same] at this
    exact this
  · rw [hpr, summands_ofSummands l' (nfl_principal hl'N)]; exact hNZ

/-- `H ≤ Z < H ⊕ P'`（`P' < M_m`）の `Z` の前線は、`H` の前線が `P'` 未満なら全て `P'` 未満 -/
theorem fr_lt_of_between {m : Nat} {H Z P' : Tm} (hMF : WNF (.M m)) (hH : WNF H) (hZ : WNF Z)
    (hPF : WNF P') (hPp : isPrincipal P' = true) (hPM : Lt P' (.M m)) (hN : NFL (summands H ++ [P']))
    (hfrH : ∀ f, f ∈ fr (.M m) H → Lt f P') (h1 : Le H Z) (h2 : Lt Z (oadd H P')) :
    ∀ f, f ∈ fr (.M m) Z → Lt f P' := by
  obtain ⟨w, rfl, hw, hwP, -⟩ := between_oadd hH hZ hPF hPp hN h1 h2
  intro f hf
  rcases fr_oadd_cases hH hw hf with hf | hf
  · exact hfrH f hf
  · have hwM : Lt w (.M m) := lt_transY hw hPF hMF hwP hPM
    have hfF := (fr_elem hw hf).1
    exact lt_of_le_of_ltY hfF hw hPF (fr_le_of_lt hMF w hw hwM f hf) hwP

/-- `Z = H ⊕ w`（`P' ≤ w < M_m`、`P'` は主要項）なら `P' < Ξ_m(Z)` -/
theorem lt_xi_of_low_tail {m : Nat} {H w P' : Tm} (hy : WNF (.Xi m (oadd H w))) (hH : WNF H) (hw : WNF w)
    (hPF : WNF P') (hPp : isPrincipal P' = true) (hN : NFL (summands H ++ summands w))
    (hPw : Le P' w) (hwM : Lt w (.M m)) : Lt P' (.Xi m (oadd H w)) := by
  have hMF := WNF.M' hy.xi.1
  have hw0 : w ≠ .zero := by
    intro e; subst e
    rcases hPw with e | h
    · subst e; cases hPp
    · exact not_lt_zero _ h
  obtain ⟨u, r, hur⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hw0)
  have huw : u ∈ summands w := by rw [hur]; exact List.mem_cons_self
  have huF := summands_WNF w hw u huw
  -- `P' ≤ u`
  have hPu : Le P' u := by
    rcases triY hPF huF.1 with h | e | h
    · exact Or.inr h
    · exact Or.inl e
    · exfalso
      have hwP : Lt w P' := lt_of_head_lt hPp hur ((lt_principal_iff huF.2 hPp).mp h)
      exact not_lt_of_leY hPF hw hPw hwP
  have huZ : u ∈ summands (oadd H w) := by
    have : summands (oadd H w) = summands H ++ summands w := by
      rw [← summands_oadd_nfl hN, ofSummands_summands _ hH, ofSummands_summands _ hw]
    rw [this]; exact List.mem_append_right _ huw
  have huM : Lt u (.M m) :=
    lt_of_le_of_ltY huF.1 hw hMF (le_of_mem_summands hw huw) hwM
  have huy : Lt u (.Xi m (oadd H w)) :=
    coll_xi0 hy u huF.1 (inC_of_mem_summands hy.xi.2.1 (xi_selfY hy) huZ) huM
  exact lt_of_le_of_ltY hPF huF.1 hy hPu huy

/-! ### 高い部分と低い部分 -/

/-- 加数が全て `M_m` 以上の `H` と `M_m` 未満の `w` の和の加数の並び -/
theorem nfl_high_low {m : Nat} {H w : Tm} (hH : WNF H) (hw : WNF w) (hMF : WNF (.M m))
    (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) (hwM : Lt w (.M m)) :
    NFL (summands H ++ summands w) := by
  refine nfl_append (nfl_summands hH) (nfl_summands hw) (fun a b ha hb => ?_)
  have haH := List.mem_of_getLast? ha
  have hbw := List.mem_of_mem_head? hb
  have haF := (summands_WNF H hH a haH).1
  have hbF := (summands_WNF w hw b hbw).1
  have hbM : Lt b (.M m) := lt_of_le_of_ltY hbF hw hMF (le_of_mem_summands hw hbw) hwM
  have hMa : Le (.M m) a := le_of_not_ltY haF hMF (hHhi a haH)
  exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hbF hMF haF hbM hMa))

/-- 高い `H` の後に `M_m` -/
theorem nfl_high_M {m : Nat} {H : Tm} (hH : WNF H) (hMF : WNF (.M m))
    (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) : NFL (summands H ++ [.M m]) := by
  refine nfl_append (nfl_summands hH) (nfl_of_wnf_principal hMF rfl) (fun a b ha hb => ?_)
  have haH := List.mem_of_getLast? ha
  have hb' : b = .M m := (by simpa using hb : Tm.M m = b).symm
  subst hb'
  have haF := (summands_WNF H hH a haH).1
  exact ne_gt_of_le (le_of_not_ltY haF hMF (hHhi a haH))

/-- 和の加数 -/
theorem summands_oadd_of_nfl {H w : Tm} (hH : WNF H) (hw : WNF w) (hN : NFL (summands H ++ summands w)) :
    summands (oadd H w) = summands H ++ summands w := by
  rw [← summands_oadd_nfl hN, ofSummands_summands _ hH, ofSummands_summands _ hw]

/-- 高い `H` を前に足しても区間の下界は保たれる（`x ≤ y < M_m`） -/
theorem lbi_oadd_high {m : Nat} {H x y : Tm} (hH : WNF H) (hMF : WNF (.M m))
    (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) (hx : WNF x) (hy : WNF y) (hxy : Le x y)
    (hyM : Lt y (.M m)) (hL : LBI x y) : LBI (oadd H x) (oadd H y) := by
  have := lbi_oadd_pre (summands H) (nfl_high_M hH hMF hHhi) hx hy hxy hyM hL
  rwa [ofSummands_summands _ hH] at this

/-- 右の引数の比較の逆 -/
theorem lt_of_oadd_lt_oadd {H x y : Tm} (hH : WNF H) (hx : WNF x) (hy : WNF y)
    (h : Lt (oadd H x) (oadd H y)) : Lt x y := by
  rcases triY hx hy with h' | e | h'
  · exact h'
  · subst e; exact absurd h (Lt.irrefl _)
  · exact absurd h (Lt.asymmY (wnf_oadd hH hy) (wnf_oadd hH hx) (oadd_lt_oadd hH hy hx h'))

/-- 区間 `(H ⊕ P', H' ⊕ P']` の `E` の 0 番目は `H` 以上 -/
theorem f0_ge_H {m : Nat} {H H' P' E : Tm} (hMF : WNF (.M m)) (hH : WNF H) (hH' : WNF H') (hPF : WNF P')
    (hE : WNF E) (hPM : Lt P' (.M m)) (hH'hi : ∀ u, u ∈ summands H' → ¬ Lt u (.M m))
    (hHH' : Le H H') (hL : LBI H H') (hAE : Lt (oadd H P') E) (hEA' : Le E (oadd H' P')) :
    Le H (fund E .zero) := by
  have hHE : Lt H E := lt_of_le_of_ltY hH (wnf_oadd hH hPF) hE (le_oadd_leftW hH hPF) hAE
  rcases triY hE hH' with h | e | h
  · exact hL E hE hHE (Or.inr h)
  · exact hL E hE hHE (Or.inl e)
  · have hL' := lbi_oadd_high hH' hMF hH'hi WNF.zero hPF (zero_le P') hPM (lbi_zero P')
    rw [oadd_zero] at hL'
    exact le_transY hH hH' (wnf_f0 hE) hHH' (hL' E hE h hEA')

/-- 形 I：`H ⊕ P' < E < H ⊕ M_m`（前線が `Ξ_m(H ⊕ P')` 未満）なら、`E[0] = H ⊕ P'` か、
`E[0] > H ⊕ P'` で `P' < Ξ_m(E[0])` -/
theorem formI {m : Nat} {H P' E : Tm} (hMF : WNF (.M m)) (hH : WNF H) (hPF : WNF P') (hE : WNF E)
    (hPp : isPrincipal P' = true) (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m))
    (hy : WNF (.Xi m (oadd H P'))) (hPy : LBI P' (.Xi m (oadd H P')))
    (hAE : Lt (oadd H P') E) (hEK : Lt E (oadd H (.M m)))
    (hfrE : ∀ f, f ∈ fr (.M m) E → Lt f (.Xi m (oadd H P')))
    (hE0 : WNF (.Xi m (fund E .zero))) :
    fund E .zero = oadd H P' ∨ (Lt (oadd H P') (fund E .zero) ∧ Lt P' (.Xi m (fund E .zero))) := by
  have hm := hy.xi.1
  have hNK := nfl_high_M hH hMF hHhi
  have hAF := wnf_oadd hH hPF
  have hHE : Le H E := Or.inr (lt_of_le_of_ltY hH hAF hE (le_oadd_leftW hH hPF) hAE)
  obtain ⟨w, rfl, hw, hwM, hNw⟩ := between_oadd hH hE hMF rfl hNK hHE hEK
  have hPw : Lt P' w := lt_of_oadd_lt_oadd hH hPF hw hAE
  have hwy : Le w (.Xi m (oadd H P')) := Or.inr (below_of_frM hm hy (Or.inl ⟨_, _, rfl⟩) rfl
    (floorLev_lt_xi hy) w hw hwM (fun f hf => hfrE f (fr_sub_of_summands (fun u hu => by
      rw [summands_oadd_of_nfl hH hw hNw]; exact List.mem_append_right _ hu) hf)))
  have hLw : LBI P' w := LBI.mono hPy hy hw hwy
  have hL := lbi_oadd_high hH hMF hHhi hPF hw (Or.inr hPw) hwM hLw
  rcases hL (oadd H w) hE hAE (Or.inl rfl) with e | hlt
  · exact Or.inl e.symm
  · refine Or.inr ⟨hlt, ?_⟩
    have hf0F := wnf_f0 hE
    have hw0 : w ≠ .zero := by
      intro e; subst e
      exact not_lt_zero _ hPw
    have hE0' : oadd H w ≠ .zero := by
      intro e
      rcases le_oadd_right hH hw with e2 | h2
      · rw [e] at e2; exact hw0 e2
      · rw [e] at h2; exact not_lt_zero _ h2
    have hf0lt := f0_lt hE hE0'
    have hHf : Le H (fund (oadd H w) .zero) :=
      le_transY hH hAF hf0F (le_oadd_leftW hH hPF) (Or.inr hlt)
    obtain ⟨w', e', hw', hw'M, hNw'⟩ := between_oadd hH hf0F hMF rfl hNK hHf
      (lt_transY hf0F hE (wnf_oadd hH hMF) hf0lt hEK)
    rw [e'] at hlt hE0 ⊢
    exact lt_xi_of_low_tail hE0 hH hw' hPF hPp hNw' (Or.inr (lt_of_oadd_lt_oadd hH hPF hw' hlt)) hw'M


/-! ### 並びの比較 -/

/-- `T < K`（並び）で、`rest` の元が全て `K` の元より小さいなら `T ++ rest < K` -/
theorem cmpList_append_lt : ∀ (T K rest : List Tm), (∀ k, k ∈ K → ∀ r, r ∈ rest → cmpP r k = .lt) →
    cmpList T K = .lt → cmpList (T ++ rest) K = .lt
  | [], [], _, _, h => by rw [cmpList_nil_nil] at h; cases h
  | [], k :: K', [], _, _ => cmpList_nil_cons k K'
  | [], k :: K', r :: rest', hk, _ => by
      show cmpList (r :: rest') (k :: K') = .lt
      have h := hk k List.mem_cons_self r List.mem_cons_self
      rw [cmpList_cons_cons_ne _ _ (by rw [h]; decide), h]
  | _ :: _, [], _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | t :: T', k :: K', rest, hk, h => by
      show cmpList (t :: (T' ++ rest)) (k :: K') = .lt
      rcases hc : cmpP t k with _ | _ | _
      · rw [cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc]
      · rw [cmpList_cons_cons_eq _ _ hc] at h ⊢
        exact cmpList_append_lt T' K' rest (fun k' hk' r hr => hk k' (List.mem_cons_of_mem _ hk') r hr) h
      · rw [cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at h; cases h

/-- `E ≥ H ⊕ M_m` の加数を `p`（`< M_m`）より大きい先頭 `pre ++ [R]` と残り（`p` 以下）に分けると、
先頭も `H ⊕ M_m` 以上 -/
theorem prefix_ge_of_ge {m : Nat} {H E p R : Tm} {pre rest : List Tm} (hMF : WNF (.M m)) (hH : WNF H)
    (hE : WNF E) (hp : WNF p) (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) (hpM : Lt p (.M m))
    (hsum : summands E = pre ++ R :: rest) (hrest : ∀ u, u ∈ rest → Le u p)
    (hEK : ¬ Lt E (oadd H (.M m))) : ¬ Lt (ofSummands (pre ++ [R])) (oadd H (.M m)) := by
  intro hlt
  apply hEK
  have hNE := nfl_summands hE
  have hT : NFL (pre ++ [R]) := by
    rw [hsum] at hNE; exact nfl_prefix hNE
  have hNM : NFL (summands H ++ summands (.M m)) := by
    rw [summands_principal (rfl : isPrincipal (Tm.M m) = true)]
    exact nfl_high_M hH hMF hHhi
  have hsK : summands (oadd H (.M m)) = summands H ++ [.M m] := by
    rw [summands_oadd_of_nfl hH hMF hNM, summands_principal (rfl : isPrincipal (Tm.M m) = true)]
  unfold Lt at hlt ⊢
  rw [cmp_eq, summands_ofSummands _ (nfl_principal hT), hsK] at hlt
  rw [cmp_eq, hsum, hsK, show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp]
  refine cmpList_append_lt _ _ rest (fun k hk r hr => ?_) hlt
  have hrE : r ∈ summands E := by rw [hsum]; simp [hr]
  have hrW := summands_WNF E hE r hrE
  have hrM : Lt r (.M m) := lt_of_le_of_ltY hrW.1 hp hMF (hrest r hr) hpM
  have hkW : WNF k ∧ isPrincipal k = true := by
    rcases List.mem_append.mp hk with hk | hk
    · exact summands_WNF H hH k hk
    · rw [List.mem_singleton.mp hk]; exact ⟨hMF, rfl⟩
  have hMk : Le (.M m) k := by
    rcases List.mem_append.mp hk with hk' | hk'
    · exact le_of_not_ltY hkW.1 hMF (hHhi k hk')
    · rw [List.mem_singleton.mp hk']; exact Or.inl rfl
  exact (lt_principal_iff hrW.2 hkW.2).mp (lt_of_lt_of_leY hrW.1 hMF hkW.1 hrM hMk)

/-! ### 近似の 0 番目の形 -/

/-- 加数 `R` での近似（種 `P'`）の 0 番目は `Ξ_m(pre ⊕ x)`（`R[0] ≤ x < R`） -/
theorem app_first_form {m : Nat} {q P' R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRi : Inv R) (hR1 : ¬ isSucc R = true) (hRS : R ≠ succM m) :
    ∃ x, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first = .Xi m (oadd (ofSummands pre) x) ∧
      WNF (.Xi m (oadd (ofSummands pre) x)) ∧ Lt P' (.Xi m (oadd (ofSummands pre) x)) ∧
      WNF x ∧ Lt x R ∧ Le (fund R .zero) x := by
  obtain ⟨A₀, hA₀, hW, hPA, -⟩ := app_first_xi G hRi hR1 hRS
  have hρ := G.ht
  have hMF := G.hMF
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hRF := G.hRF
  have hPF := G.hPF
  have hR0 := G.hR0
  have fin : ∀ x, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first =
      .Xi m (oadd (ofSummands pre) x) → WNF x → Lt x R → Le (fund R .zero) x →
      ∃ x, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first = .Xi m (oadd (ofSummands pre) x) ∧
        WNF (.Xi m (oadd (ofSummands pre) x)) ∧ Lt P' (.Xi m (oadd (ofSummands pre) x)) ∧
        WNF x ∧ Lt x R ∧ Le (fund R .zero) x := by
    intro x hfx hx hxR hfx0
    have e : A₀ = oadd (ofSummands pre) x := by
      rw [hfx] at hA₀; exact (Tm.Xi.inj hA₀).2.symm
    rw [e] at hW hPA
    exact ⟨x, hfx, hW, hPA, hx, hxR, hfx0⟩
  cases hdR : dom R with
  | zero => exact absurd ((dom_eq_zero_iff hRF).mp hdR) hR0
  | one => exact absurd ((dom_eq_one_iff hRF).mp hdR) hR1
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    have hxF := hRN.props.nf 0
    refine fin (nsum P' (fundNat R 0)) ?_ (G.hyF hxF) (G.hyR hxF (hRN.props.lt 0)) ?_
    · unfold SeqD.first; rw [app_xi_dom_nat hr]; exact app_xi_nat hr hPF hxF
    · rw [fund_zero_omega hdR]; exact le_nsum_right hPF hxF
  | big σ =>
    have hr : (info R).seq.dom = .big σ := hdR
    have hB := hRi.2 σ hdR
    have hσF := hB.props.σF
    have hσ0 := hB.props.pos
    by_cases hσρ : Lt σ (.Xi m q)
    · have hxF := hB.props.nf .zero WNF.zero hσ0
      refine fin (nsum P' (fundBig R .zero)) ?_ (G.hyF hxF)
        (G.hyR hxF (hB.props.lt .zero WNF.zero hσ0)) ?_
      · unfold SeqD.first; rw [app_xi_big_dom hr hσρ]; exact app_xi_big hPF hxF
      · rw [fund_zero_big hdR]; exact le_nsum_right hPF hxF
    · rcases cof_split hρ G.hRq hB hσρ with e | ⟨-, eR, -⟩
      · subst e
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        have hPM := G.hPM
        have hxF := hB.props.nf P' hPF hPM
        refine fin (fundBig R P') ?_ hxF (hB.props.lt P' hPF hPM) ?_
        · unfold SeqD.first
          rw [app_xi_M_dom hr hτ, app_xi_M_nat hr hτ, gam_xi_M_succ, gam_xi_M_zero]
          show Tm.Xi m (combine (.xi m) pre .zero .zero (fundBig R P')) = _
          rw [combine_xi m pre WNF.zero hxF]
          show Tm.Xi m (oadd (ofSummands pre) (nsum .zero (fundBig R P'))) = _
          rw [zero_nsum _ hxF]
        · rw [fund_zero_big hdR]
          exact bigProps_mono_le hB.props WNF.zero hPF (zero_le P') hPM
      · exact absurd eR hRS

/-- 底の閉包が種 `p`（前線の最大元）の近似になる場合の 0 番目 -/
theorem base_f0_seeded {m : Nat} {E p R : Tm} {pre : List Tm} {r : SeqD} (hE : WNF (.Xi m E))
    (hE0 : E ≠ .zero) (hs : ¬ isSucc E = true) (hp : maxL (frB (.Xi m E) (.Xi m E)) = some p)
    (h1 : ¬ ltB p (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
      (lastS (info E).sums) .zero .zero).first = true)
    (h2 : (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
      (lastS (info E).sums) .zero .zero).first ≠ p)
    (hsplit : splitGtD p (info E).sums = some (pre, R, r)) (hpR : Lt p R) :
    fund (base (.Xi m E)) .zero = (SeqD.app (.Xi m E) (.xi m) pre R r p .zero).first := by
  rw [base_f0_eq hE]
  unfold mahloVK
  rw [ite_eq_right hE0, ite_eq_right hs]
  dsimp only
  rw [hp]
  dsimp only
  rw [ite_eq_right h1, ite_eq_right h2, hsplit]
  dsimp only
  rw [mkApp_xi (ltB_iff.mpr hpR)]


/-! ### 種つきの近似の区間の評価 -/

/-- 種つきの近似 `Ξ_m(H ⊕ P')`・`Ξ_m(H' ⊕ P')` の区間に現れる関連する `E`（前線が `Ξ_m(H ⊕ P')` 未満）について、
`Ξ_m(F) ≤ base(Ξ_m(E))[0]` となる `F`（`F = H ⊕ P'` か、`H ⊕ P' < F < E` で関連する） -/
theorem seeded_cond {m : Nat} {H H' P' B : Tm} (hHF : WNF H) (hH'F : WNF H') (hPF : WNF P')
    (hPp : isPrincipal P' = true) (hP1 : Lt one P') (hPM : Lt P' (.M m))
    (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) (hH'hi : ∀ u, u ∈ summands H' → ¬ Lt u (.M m))
    (hHH' : Le H H') (hL : LBI H H')
    (hy : WNF (.Xi m (oadd H P'))) (hA'F : WNF (oadd H' P')) (hA'S : Lt (oadd H' P') (succM m))
    (hBF : WNF B) (hcl : XiClosed m P' B) (hA'B : Lt (oadd H' P') B)
    (hPy : LBI P' (.Xi m (oadd H P'))) (hfrH : ∀ f, f ∈ fr (.M m) H → Lt f P') :
    ∀ E, WNF (.Xi m E) → Lt (oadd H P') E → Le E (oadd H' P') →
      Lt (.Xi m (oadd H P')) (.Xi m E) → (∀ f, f ∈ fr (.M m) E → Lt f (.Xi m (oadd H P'))) →
      ∃ F, WNF (.Xi m F) ∧ Le (.Xi m F) (fund (base (.Xi m E)) .zero) ∧
        (F = oadd H P' ∨ (Lt (oadd H P') F ∧ Lt F E ∧ Lt (.Xi m (oadd H P')) (.Xi m F))) := by
  intro E hE hAE hEA' hrel hfrE
  have hm := hy.xi.1
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hAF := wnf_oadd hHF hPF
  have hEF := hE.xi.2.1
  have hNA : NFL (summands H ++ summands P') := nfl_high_low hHF hPF hMF hHhi hPM
  have hNA' : NFL (summands H ++ [P']) := by rw [← summands_principal hPp]; exact hNA
  have hNA2 : NFL (summands H' ++ summands P') := nfl_high_low hH'F hPF hMF hH'hi hPM
  have hNA'' : NFL (summands H' ++ [P']) := by rw [← summands_principal hPp]; exact hNA2
  have hEB : Lt E B := lt_of_le_of_ltY hEF hA'F hBF hEA' hA'B
  -- `P' < Ξ_m(A)`、`A` の前線は `P'` 以下
  have hPA : P' ∈ summands (oadd H P') := by
    rw [summands_oadd_of_nfl hHF hPF hNA, summands_principal hPp]; simp
  have hPy' : Lt P' (.Xi m (oadd H P')) := summand_lt_xi hy hPA hPM
  have hfrA : ∀ f, f ∈ fr (.M m) (oadd H P') → Le f P' := by
    intro f hf
    rcases fr_oadd_cases hHF hPF hf with hf | hf
    · exact Or.inr (hfrH f hf)
    · exact fr_le_of_lt hMF P' hPF hPM f hf
  -- 関連性：`P' < Ξ_m(D)`、`A < D` なら `Ξ_m(A) < Ξ_m(D)`
  have relh : ∀ D, WNF (.Xi m D) → Lt (oadd H P') D → Lt P' (.Xi m D) →
      Lt (.Xi m (oadd H P')) (.Xi m D) := fun D hD hAD hPD =>
    xi_step hy hD hAD (fun f hf =>
      lt_of_le_of_ltY (fr_elem hAF hf).1 hPF hD (hfrA f hf) hPD)
  -- `E` の前線には `P'` 以上の元がある
  obtain ⟨u, hu, hPu⟩ : ∃ u, u ∈ fr (.M m) E ∧ Le P' u := by
    rcases fr_all_or_exists (.M m) E P' with hall | ⟨u, hu, huP⟩
    · exfalso
      have h1 := hcl E hE hEB hall
      exact Lt.asymmY hE hPF h1 (lt_transY hPF hy hE hPy' hrel)
    · exact ⟨u, hu, le_of_not_ltY (fr_elem hEF hu).1 hPF huP⟩
  have huF := (fr_elem hEF hu).1
  have hE0 : E ≠ .zero := fun e => by rw [e] at hAE; exact not_lt_zero _ hAE
  have hES : E ≠ succM m := fun e => by
    rw [e] at hEA'
    exact not_lt_of_leY hSF hA'F hEA' hA'S
  by_cases hs : isSucc E = true
  · -- 後者：`F = E - 1`
    have hpF := xi_pred_wnf hE hs
    have hplt := xi_pred_lt_base_f0 hE hs
    have hAp : Le (oadd H P') (predT E) := le_pred hEF hs hAF hAE
    rcases hAp with e | hlt
    · exact ⟨predT E, hpF, Or.inr hplt, Or.inl e.symm⟩
    · refine ⟨predT E, hpF, Or.inr hplt, Or.inr ⟨hlt, lt_predT hEF hs, relh _ hpF hlt ?_⟩⟩
      obtain ⟨ys, hys⟩ := summands_of_isSucc hs
      have hu' : u ∈ fr (.M m) (predT E) := by
        obtain ⟨v, hv, huv⟩ := mem_fr_iff.mp hu
        rw [hys] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact mem_fr_iff.mpr ⟨v, by rw [summands_predT hEF hys]; exact hv, huv⟩
        · exfalso
          rw [List.mem_singleton.mp hv] at huv
          have h1M : Lt (Tm.Psi (.Om .zero) .zero) (.M m) := lt_transY WNF.one hPF hMF hP1 hPM
          have hu1 : u = one := by
            simp only [one, fr, h1M, ↓reduceIte, List.mem_singleton] at huv
            exact huv
          rw [hu1] at hPu
          exact not_lt_of_leY hPF WNF.one hPu hP1
      exact lt_of_le_of_ltY hPF huF hpF hPu (fr_lt_xi hpF hu')
  -- 極限
  have hRinv : ∀ R, R ∈ summands E → Inv R := fun R hR => inv_of R (summands_WNF E hEF R hR).1
  obtain ⟨hE0F, hC1⟩ := xi_f0_le_base_f0 hE hE0 hES
  have hf0F := wnf_f0 hEF
  have hf0lt := f0_lt hEF hE0
  have good : fund E .zero = oadd H P' ∨ (Lt (oadd H P') (fund E .zero) ∧ Lt P' (.Xi m (fund E .zero))) →
      ∃ F, WNF (.Xi m F) ∧ Le (.Xi m F) (fund (base (.Xi m E)) .zero) ∧
        (F = oadd H P' ∨ (Lt (oadd H P') F ∧ Lt F E ∧ Lt (.Xi m (oadd H P')) (.Xi m F))) := by
    intro h
    rcases h with e | ⟨hlt, hP0⟩
    · exact ⟨fund E .zero, hE0F, hC1, Or.inl e⟩
    · exact ⟨fund E .zero, hE0F, hC1, Or.inr ⟨hlt, hf0lt, relh _ hE0F hlt hP0⟩⟩
  have hKF : WNF (oadd H (.M m)) := wnf_oadd hHF hMF
  by_cases hK : Lt E (oadd H (.M m))
  · exact good (formI hMF hHF hPF hEF hPp hHhi hy hPy hAE hK hfrE hE0F)
  -- 形 II：種の閉包
  have seeded : Le (.Xi m (fund E .zero)) P' →
      ∃ F, WNF (.Xi m F) ∧ Le (.Xi m F) (fund (base (.Xi m E)) .zero) ∧
        (F = oadd H P' ∨ (Lt (oadd H P') F ∧ Lt F E ∧ Lt (.Xi m (oadd H P')) (.Xi m F))) := by
    intro hle0
    -- 前線の最大元 `p`
    have hufr' : u ∈ frB (.Xi m E) (.Xi m E) := by rw [frB_eq_fr]; exact (fr_rho_iff hE).mpr hu
    obtain ⟨p, hp⟩ : ∃ p, maxL (frB (.Xi m E) (.Xi m E)) = some p := by
      cases h : maxL (frB (.Xi m E) (.Xi m E)) with
      | none => rw [maxL_none h] at hufr'; cases hufr'
      | some p => exact ⟨p, rfl⟩
    have hpfr : p ∈ fr (.M m) E := (fr_rho_iff hE).mp (by rw [← frB_eq_fr]; exact maxL_mem hp)
    obtain ⟨hpF, hpM, hpp, -, -⟩ := fr_elem hEF hpfr
    have hup : Le u p := maxL_le (fun x hx => by rw [frB_eq_fr] at hx; exact (fr_elem hE hx).1)
      hp u hufr'
    have hPp' : Le P' p := le_transY hPF huF hpF hPu hup
    -- 素の近似の 0 番目は `Ξ_m(E[0])`
    obtain ⟨R0, x0, hsq, hfirst, -, -, -, -, -, -, hx0⟩ := s0_first_xi hE hE0 hs hES hRinv
    have hR0q : R0 ∈ summands E := by rw [hsq]; simp
    have hR0W := summands_WNF E hEF R0 hR0q
    have hR0ns : ¬ isSucc R0 = true := by rw [← isSucc_of_last hsq hR0W.2]; exact hs
    have hx0F : WNF x0 := by rw [hx0]; exact wnf_f0 hR0W.1
    have he : fund E .zero = xa (summands E).dropLast .zero x0 := by
      rw [f0_split _ hEF hsq hR0ns, ← hx0]
      show _ = oadd (ofSummands (summands E).dropLast) (nsum .zero x0)
      rw [zero_nsum x0 hx0F]
    have hs0 : (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums) (lastS (info E).sums)
        .zero .zero).first = .Xi m (fund E .zero) := by rw [hfirst, he]
    have h1 : ¬ ltB p (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
        (lastS (info E).sums) .zero .zero).first = true := by
      rw [hs0]; intro h
      exact not_lt_of_leY hE0F hpF (le_transY hE0F hPF hpF hle0 hPp') (ltB_iff.mp h)
    have h2 : (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
        (lastS (info E).sums) .zero .zero).first ≠ p := by
      rw [hs0]; intro e
      have hPe : P' = .Xi m (fund E .zero) := le_antisymmY hPF hE0F (by rw [e]; exact hPp') hle0
      have h3 := hcl (fund E .zero) hE0F (lt_transY hf0F hEF hBF hf0lt hEB)
        (fun f hf => by rw [hPe]; exact fr_lt_xi hE0F hf)
      rw [hPe] at h3
      exact Lt.irrefl _ h3
    -- 分割
    have hKE : Le (oadd H (.M m)) E := le_of_not_ltY hEF hKF hK
    cases hsplit : splitGtD p (info E).sums with
    | none =>
      exfalso
      have hall := splitGtD_none hEF hpF hsplit
      have hEM : Lt E (.M m) := lt_of_summands_lt hEF rfl (fun v hv =>
        lt_of_le_of_ltY (summands_WNF E hEF v hv).1 hpF hMF (hall v hv) hpM)
      exact not_lt_of_leY hMF hEF (le_transY hMF hKF hEF (le_oadd_right hHF hMF) hKE) hEM
    | some val =>
      obtain ⟨pre, R, r⟩ := val
      obtain ⟨rest, hsum, hr, hpR, hrest⟩ := splitGtD_spec hEF hpF hsplit
      subst hr
      have hbase := base_f0_seeded hE hE0 hs hp h1 h2 hsplit hpR
      have G : XG m E p pre rest R := ⟨hE, hsum, hpF, hpR, hpM, Or.inr hpp⟩
      have hRq : R ∈ summands E := by rw [hsum]; simp
      have hRW := summands_WNF E hEF R hRq
      have hRinv' := hRinv R hRq
      have hR1 : ¬ isSucc R = true := not_succ_of_gt hpF hpp hRW.2 hpR
      have hRS : R ≠ succM m := by
        intro e
        have hRE : Le R E := le_of_mem_summands hEF hRq
        rw [e] at hRE
        exact not_lt_of_leY hSF hEF hRE (lt_of_le_of_ltY hEF hA'F hSF hEA' hA'S)
      obtain ⟨x, hfx, hWx, hpx, hxF, hxR, hfx0⟩ := app_first_form G hRinv' hR1 hRS
      rw [hbase, hfx]
      have hpreF := G.hpreF
      have hTF := G.hTF
      have hA₀F : WNF (oadd (ofSummands pre) x) := wnf_oadd hpreF hxF
      -- `T = pre ⊕ R ≥ H ⊕ M_m`
      have hTK : ¬ Lt (ofSummands (pre ++ [R])) (oadd H (.M m)) :=
        prefix_ge_of_ge hMF hHF hEF hpF hHhi hpM hsum hrest hK
      have hHT : Lt H (ofSummands (pre ++ [R])) :=
        lt_of_lt_of_leY hHF hKF hTF (lt_oadd_left hHF hMF (by intro e; cases e))
          (le_of_not_ltY hTF hKF hTK)
      -- `T ≤ E`
      have hNE := nfl_summands hEF
      have hTE : Le (ofSummands (pre ++ [R])) E := by
        have e : summands E = (pre ++ [R]) ++ rest := by rw [hsum]; simp
        have hN2 : NFL ((pre ++ [R]) ++ rest) := by rw [← e]; exact hNE
        have : E = oadd (ofSummands (pre ++ [R])) (ofSummands rest) := by
          rw [← ofSummands_summands E hEF, e, ofSummands_append hN2]
        rw [this]
        exact le_oadd_leftW hTF (wnf_ofSummands (nfl_append_right hN2))
      -- `T` の加数は全て `p` より大きい
      have hTgt : ∀ s, s ∈ pre ++ [R] → Lt p s := by
        intro s hs'
        rcases List.mem_append.mp hs' with hs' | hs'
        · have hsW := G.hNT.1 s (List.mem_append_left _ hs')
          have hRs : cmp R s ≠ .gt := nfl_append_ge G.hNT s hs' R (by simp)
          exact lt_of_lt_of_leY hpF hRW.1 hsW.1 hpR (le_of_ne_gtY hRW.1 hsW.1 hRs)
        · rw [List.mem_singleton.mp hs']; exact hpR
      -- `T ≤ H'`
      have hTH' : Le (ofSummands (pre ++ [R])) H' := by
        rcases triY hTF hH'F with h | e | h
        · exact Or.inr h
        · exact Or.inl e
        · exfalso
          have hTA' : Lt (ofSummands (pre ++ [R])) (oadd H' P') := by
            rcases le_transY hTF hEF hA'F hTE hEA' with e | h'
            · exfalso
              have hsT := G.hsT
              rw [e, summands_oadd_of_nfl hH'F hPF hNA2, summands_principal hPp] at hsT
              have hRP : R = P' := by
                have h' := congrArg List.getLast? hsT
                simp at h'
                first | exact h'.symm | exact h'
              rw [hRP] at hpR
              exact not_lt_of_leY hPF hpF hPp' hpR
            · exact h'
          obtain ⟨w, ew, hw, hwP, hNw⟩ := between_oadd hH'F hTF hPF hPp hNA'' (Or.inr h) hTA'
          have hw0 : w ≠ .zero := by
            intro e0; rw [e0, oadd_zero] at ew; rw [ew] at h; exact Lt.irrefl _ h
          obtain ⟨v, rr, hvr⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hw0)
          have hvw : v ∈ summands w := by rw [hvr]; exact List.mem_cons_self
          have hvT : v ∈ pre ++ [R] := by
            rw [← G.hsT, ew, summands_oadd_of_nfl hH'F hw hNw]
            exact List.mem_append_right _ hvw
          have hvF := (summands_WNF w hw v hvw).1
          have hvP : Lt v P' := lt_of_le_of_ltY hvF hw hPF (le_of_mem_summands hw hvw) hwP
          exact Lt.asymmY hpF hvF (hTgt v hvT) (lt_of_lt_of_leY hvF hPF hpF hvP hPp')
      have hT0 : Le H (fund (ofSummands (pre ++ [R])) .zero) := hL _ hTF hHT hTH'
      have hfT : fund (ofSummands (pre ++ [R])) .zero = oadd (ofSummands pre) (fund R .zero) :=
        f0_split pre hTF G.hsT hR1
      have hA₀H : Le H (oadd (ofSummands pre) x) := by
        refine le_transY hHF (wnf_f0 hTF) hA₀F hT0 ?_
        rw [hfT]; exact oadd_le_oadd hpreF (wnf_f0 hRW.1) hxF hfx0
      have hA₀T : Lt (oadd (ofSummands pre) x) (ofSummands (pre ++ [R])) := by
        rw [G.hTe]; exact oadd_lt_oadd hpreF hxF hRW.1 hxR
      have hA₀E : Lt (oadd (ofSummands pre) x) E := lt_of_lt_of_leY hA₀F hTF hEF hA₀T hTE
      have hPx : Lt P' (.Xi m (oadd (ofSummands pre) x)) := lt_of_le_of_ltY hPF hpF hWx hPp' hpx
      rcases triY hAF hA₀F with hlt | e | hgt
      · exact ⟨_, hWx, Or.inl rfl, Or.inr ⟨hlt, hA₀E, relh _ hWx hlt hPx⟩⟩
      · exact ⟨_, hWx, Or.inl rfl, Or.inl e.symm⟩
      · exfalso
        have hfr0 := fr_lt_of_between hMF hHF hA₀F hPF hPp hPM hNA' hfrH hA₀H hgt
        have h3 := hcl _ hWx (lt_transY hA₀F hEF hBF hA₀E hEB) hfr0
        exact Lt.asymmY hWx hPF h3 hPx
  rcases triY hAF hf0F with hlt | e | hgt
  · by_cases hP0 : Lt P' (.Xi m (fund E .zero))
    · exact good (Or.inr ⟨hlt, hP0⟩)
    · exact seeded (le_of_not_ltY hPF hE0F hP0)
  · exact good (Or.inl e.symm)
  · have hHf := f0_ge_H hMF hHF hH'F hPF hEF hPM hH'hi hHH' hL hAE hEA'
    have hfr0 := fr_lt_of_between hMF hHF hf0F hPF hPp hPM hNA' hfrH hHf hgt
    exact seeded (Or.inr (hcl _ hE0F (lt_transY hf0F hEF hBF hf0lt hEB) hfr0))


/-! ### `M_m` と `M_m⁺` の間の主要項 -/

theorem lev_succM (m : Nat) : lev (succM m) = m + 1 := by
  simp only [succM, lev]
  exact Nat.max_eq_right (by omega)

/-- `M_m⁺` は `n ≥ m+1` の `Ξ_n(d)` 未満 -/
theorem succM_lt_xi {m n : Nat} {d : Tm} (hm : 1 ≤ m) (hX : WNF (.Xi n d)) (hn : m + 1 ≤ n) :
    Lt (succM m) (.Xi n d) := by
  have hMF := WNF.M' hm
  rcases Nat.lt_or_eq_of_le hn with hn | rfl
  · exact lt_of_lev_lt' (by rw [lev_succM]; simp only [lev]; exact hn)
  · have hOF : IsOF (.Xi (m + 1) d) := Or.inl ⟨_, _, rfl⟩
    have hMx : Lt (.M m) (.Xi (m + 1) d) := bot_ltY rfl (by simp only [lev]; omega) rfl rfl hX
    have hpl : WNF (.plus (.M m) one) := succT_WNF hMF
    have h3 : Lt (.plus (.M m) one) (.Xi (m + 1) d) := (lt_plus_prin_iffY hpl rfl).mpr hMx
    exact (lt_om_OFG hOF hX).mpr h3

/-- `M_m` と `M_m⁺` の間の主要項は `Ψ_{M_m⁺}(Y)` -/
theorem prin_between_M {m : Nat} {R : Tm} (hm : 1 ≤ m) (hR : WNF R) (hRp : isPrincipal R = true)
    (h1 : Lt (.M m) R) (h2 : Lt R (succM m)) : ∃ Y, R = .Psi (succM m) Y := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hl1 := lev_le_of_lt_gen h1
  have hl2 := lev_le_of_lt_gen h2
  rw [lev_succM] at hl2
  have hone : Lt one R :=
    lt_transY WNF.one hMF hR (lt_of_lev_lt' (by show (1 : Nat) < m + 1; omega)) h1
  have hSC : ∀ a, inC (succM m) a R = true := by
    intro a
    show inC (.Om (.plus (.M m) one)) a R = true
    rw [inC_om, inC_plus, inC_M, Bool.true_and]
    exact inC_of_lt_node (Or.inr ⟨_, _, rfl⟩) hone
  cases R with
  | zero => cases hRp
  | plus _ _ => cases hRp
  | M n =>
    exfalso
    simp only [lev] at hl1 hl2
    have : n = m := by omega
    subst this
    exact Lt.irrefl _ h1
  | Om c =>
    exfalso
    have hcF := hR.om.1
    have hMc : Lt (.M m) c := (lt_M_omY hm hR).mp h1
    have hcS : Lt c (.plus (.M m) one) := lt_om_iffG.mp h2
    exact not_lt_of_leY hcF hMF (le_of_lt_succT hcF hMF hcS) hMc
  | Xi n d =>
    exfalso
    simp only [lev] at hl1
    exact Lt.asymmY hR hSF h2 (succM_lt_xi hm hR (by omega))
  | Psi p a =>
    have hpF := hR.psi.piF
    rcases hR.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, d, rfl⟩
    · exfalso
      have : lev (Tm.Psi (.Om .zero) a) = 1 := rfl
      rw [this] at hl1
      simp only [lev] at hl1
      omega
    · by_cases hc : c = .plus (.M m) one
      · subst hc; exact ⟨a, rfl⟩
      · exfalso
        have hcF := hpF.om.1
        have hMc : Lt (.M m) c := (lt_M_omY hm hpF).mp (lt_transY hMF hR hpF h1 (lt_psi_targetY hR))
        have hle : Le (.plus (.M m) one) c := succT_leY hMF hcF hMc
        have hlt : Lt (.plus (.M m) one) c := by
          rcases hle with e | h
          · exact absurd e.symm hc
          · exact h
        have hSp : Lt (succM m) (.Om c) := lt_om_iffG.mpr hlt
        exact Lt.asymmY hR hSF h2 (coll_psiY hR hSF (hSC a) hSp)
    · exfalso
      simp only [lev] at hl1
      exact Lt.asymmY hR hSF h2 (coll_psiY hR hSF (hSC a) (succM_lt_xi hm hpF (by omega)))

/-- 崩壊の近似 `app`（`Ψ_π` を作る）の項は `Ψ_π(·)` の形 -/
theorem app_psi_shape {τ π R P c : Tm} {pre : List Tm} {r : SeqD} (n : Nat) (ξ : Tm) :
    ((SeqD.app τ (.psi π) pre R r P c).dom = .omega →
      ∃ a, (SeqD.app τ (.psi π) pre R r P c).nat n = .Psi π a) ∧
    (∃ a, (SeqD.app τ (.psi π) pre R r P c).big ξ = .Psi π a) := by
  refine ⟨fun hd => ?_, ⟨_, rfl⟩⟩
  cases hr : r.dom with
  | big σ =>
    have hl : ltB σ τ = false := by
      cases h : ltB σ τ with
      | false => rfl
      | true => simp [SeqD.dom, hr, h] at hd
    simp only [SeqD.nat, hr, hl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl⟩
  | _ => simp only [SeqD.nat, hr]; exact ⟨_, rfl⟩

/-- `Ψ_{M_m⁺}(Y)` の基本列の項の加数は全て `M_m` 以上 -/
theorem psiS_fs_high {m : Nat} {Y : Tm} (hm : 1 ≤ m) (hR : WNF (.Psi (succM m) Y)) :
    (dom (.Psi (succM m) Y) = .omega → ∀ n u, u ∈ summands (fundNat (.Psi (succM m) Y) n) →
      ¬ Lt u (.M m)) ∧
    (∀ σ, dom (.Psi (succM m) Y) = .big σ → ∀ ξ, WNF ξ → Lt ξ σ →
      ∀ u, u ∈ summands (fundBig (.Psi (succM m) Y) ξ) → ¬ Lt u (.M m)) := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hMS : Lt (.M m) (succM m) :=
    (lt_M_omY hm hSF).mpr (lt_plus_leftY (succT_WNF hMF))
  have hok : ∀ u, WNF u → (u = .M m ∨ ∃ a, u = .Psi (succM m) a) → ¬ Lt u (.M m) := by
    intro u hu h
    rcases h with rfl | ⟨a, rfl⟩
    · exact Lt.irrefl _
    · exact Lt.asymmY hMF hu (coll_psiY hu hMF (inC_M m _ _) hMS)
  have hP := props_all _ hR
  have hshape : (∀ n, (cs (succM m) Y).dom = .omega →
        (∃ a, (cs (succM m) Y).nat n = .Psi (succM m) a) ∨
        ∃ B k, (cs (succM m) Y).nat n = mulNat B k ∧ isPrincipal B = true ∧
          (B = .M m ∨ ∃ a, B = .Psi (succM m) a)) ∧
      (∀ σ ξ, (cs (succM m) Y).dom = .big σ → ∃ a, (cs (succM m) Y).big ξ = .Psi (succM m) a) := by
    have hYF := hR.psi.aF
    by_cases hY0 : Y = .zero
    · subst hY0
      have e : cs (succM m) .zero = .mul (.M m) 2 := by
        show cs (.Om (.plus (.M m) one)) .zero = _
        rw [cs_zero_om, if_neg (by intro h; cases h)]
        rfl
      rw [e]
      refine ⟨fun n _ => Or.inr ⟨.M m, n + 2, rfl, rfl, Or.inl rfl⟩, fun σ ξ hd => ?_⟩
      simp [SeqD.dom] at hd
    by_cases hs : isSucc Y = true
    · have e : cs (succM m) Y = .mul (.Psi (succM m) (pred Y)) 2 := cs_succ_om hYF hs
      rw [e]
      refine ⟨fun n _ => Or.inr ⟨_, n + 2, rfl, rfl, Or.inr ⟨_, rfl⟩⟩, fun σ ξ hd => ?_⟩
      simp [SeqD.dom] at hd
    · rw [cs_lim hYF hY0 hs]
      rcases limitSeq_cases (τ := succM m) (ceil := succM m) (xs := (info Y).sums) with
        e | ⟨c', e | ⟨s, e⟩⟩
      · rw [e]
        exact ⟨fun n hd => by simp [SeqD.dom] at hd, fun σ ξ hd => by simp [SeqD.dom] at hd⟩
      · rw [e]
        exact ⟨fun n hd => Or.inl ((app_psi_shape n .zero).1 hd), fun σ ξ _ => (app_psi_shape 0 ξ).2⟩
      · rw [e]
        exact ⟨fun n _ => Or.inl ⟨_, rfl⟩, fun σ ξ _ => ⟨_, rfl⟩⟩
  refine ⟨fun hd n u hu => ?_, fun σ hd ξ hξ hξσ u hu => ?_⟩
  · have hxF := (hP.1 hd).nf n
    have huW := summands_WNF _ hxF u hu
    have hd' : (cs (succM m) Y).dom = .omega := hd
    rw [fundNat_psi] at hu
    rcases hshape.1 n hd' with ⟨a, e⟩ | ⟨B, k, e, hBp, hB⟩
    · rw [e, summands_principal rfl, List.mem_singleton] at hu
      exact hok u huW.1 (Or.inr ⟨a, hu⟩)
    · rw [e, summands_mulNat hBp, List.mem_replicate] at hu
      rw [hu.2] at huW ⊢
      exact hok B huW.1 hB
  · have hxF := (hP.2 σ hd).nf ξ hξ hξσ
    have huW := summands_WNF _ hxF u hu
    rw [fundBig_psi] at hu
    obtain ⟨a, e⟩ := hshape.2 σ ξ hd
    rw [e, summands_principal rfl, List.mem_singleton] at hu
    exact hok u huW.1 (Or.inr ⟨a, hu⟩)


/-! ### 段の区間の下界 -/

/-- 区間の関連する `E` の評価（一般形）：前線が全て `Ξ_m(A)` 未満の関連する `E` について、
`Ξ_m(F) ≤ base(Ξ_m(E))[0]` となる `F`（`F = A` か、`A < F < E` で関連する）があれば -/
theorem xi_le_base_f0_relF {m : Nat} {A A' : Tm} (hA : WNF (.Xi m A)) (hA'F : WNF A')
    (H : ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      (∀ f, f ∈ fr (.M m) E → Lt f (.Xi m A)) →
      ∃ F, WNF (.Xi m F) ∧ Le (.Xi m F) (fund (base (.Xi m E)) .zero) ∧
        (F = A ∨ (Lt A F ∧ Lt F E ∧ Lt (.Xi m A) (.Xi m F)))) :
    ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero) := by
  intro E hE hAE hEA' hrel
  refine WellFounded.induction wellFounded_isNF
    (C := fun a => WNF (.Xi m a.1) → Lt A a.1 → Le a.1 A' → Lt (.Xi m A) (.Xi m a.1) →
      Le (.Xi m A) (fund (base (.Xi m a.1)) .zero))
    ⟨E, hE.xi.2.1⟩ ?_ hE hAE hEA' hrel
  intro ⟨E, hEF⟩ ih hE hAE hEA' hrel
  dsimp only at hE hAE hEA' hrel ⊢
  rcases fr_all_or_exists (.M m) E (.Xi m A) with hfr | ⟨f, hf, hfA⟩
  · obtain ⟨F, hFW, hFb, hF⟩ := H E hE hAE hEA' hrel hfr
    rcases hF with e | ⟨hAF', hFE, hrelF⟩
    · rw [← e]; exact hFb
    · have hFF := hFW.xi.2.1
      have ih' := ih ⟨F, hFF⟩ hFE hFW hAF' (Or.inr (lt_of_lt_of_leY hFF hEF hA'F hFE hEA')) hrelF
      have hreg0 : IsRegY (.Xi m F) := Or.inr (Or.inr (Or.inr ⟨m, _, rfl⟩))
      have hb0F : WNF (base (.Xi m F)) := wnf_base hFW hreg0
      have h1 : Lt (fund (base (.Xi m F)) .zero) (.Xi m F) :=
        lt_transY (wnf_f0 hb0F) hb0F hFW
          (f0_lt hb0F (by show Tm.Psi _ _ ≠ .zero; intro e; cases e)) (base_lt hFW hreg0)
      have hy0F := wnf_f0 (wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩))))
      exact le_transY hA hFW hy0F (Or.inr (lt_of_le_of_ltY hA (wnf_f0 hb0F) hFW ih' h1)) hFb
  · have hfF := (fr_elem hEF hf).1
    exact xi_le_base_f0_of_front hA hE hf (le_of_not_ltY hfF hA hfA)

/-- 種つきの近似の 1 段：`LBI (Ξ_m(H ⊕ P')) (Ξ_m(H' ⊕ P'))`（`H ≤ H'` は高い、`LBI H H'`、種 `P'` は閉じていて
`LBI P' (Ξ_m(H ⊕ P'))`、`H`・`H'` の前線は `P'` 未満） -/
theorem lbi_seeded {m : Nat} {H H' P' B : Tm} (hHF : WNF H) (hH'F : WNF H') (hPF : WNF P')
    (hPp : isPrincipal P' = true) (hP1 : Lt one P') (hPM : Lt P' (.M m))
    (hHhi : ∀ u, u ∈ summands H → ¬ Lt u (.M m)) (hH'hi : ∀ u, u ∈ summands H' → ¬ Lt u (.M m))
    (hHH' : Le H H') (hL : LBI H H')
    (hy : WNF (.Xi m (oadd H P'))) (hy' : WNF (.Xi m (oadd H' P'))) (hA'S : Lt (oadd H' P') (succM m))
    (hBF : WNF B) (hcl : XiClosed m P' B) (hA'B : Lt (oadd H' P') B)
    (hPy : LBI P' (.Xi m (oadd H P'))) (hfrH : ∀ f, f ∈ fr (.M m) H → Lt f P')
    (hfrH' : ∀ f, f ∈ fr (.M m) H' → Lt f P') :
    LBI (.Xi m (oadd H P')) (.Xi m (oadd H' P')) := by
  have hm := hy.xi.1
  have hMF := WNF.M' hm
  have hA'F := hy'.xi.2.1
  have hNA : NFL (summands H ++ summands P') := nfl_high_low hHF hPF hMF hHhi hPM
  have hPA : P' ∈ summands (oadd H P') := by
    rw [summands_oadd_of_nfl hHF hPF hNA, summands_principal hPp]; simp
  have hPy' : Lt P' (.Xi m (oadd H P')) := summand_lt_xi hy hPA hPM
  refine lbi_xi_step hy hy' (fun f hf => ?_) (fun E hE hAE hEA' hrel =>
    xi_le_base_f0_relF hy hA'F (seeded_cond hHF hH'F hPF hPp hP1 hPM hHhi hH'hi hHH' hL hy hA'F hA'S
      hBF hcl hA'B hPy hfrH) E hE hAE hEA' hrel)
  have hfF := (fr_elem hA'F hf).1
  rcases fr_oadd_cases hH'F hPF hf with hf | hf
  · exact Or.inr (lt_transY hfF hPF hy (hfrH' f hf) hPy')
  · exact le_transY hfF hPF hy (fr_le_of_lt hMF P' hPF hPM f hf) (Or.inr hPy')


/-! ### 包による段の補題 -/

/-- `Ξ` の持ち上げの 1 段（包の形）：`A'` が `Ξ_m(A)` より大きい全ての `d` について `C(A', d)` に入れば、
`A'` より上の `E` は区間に現れない -/
theorem lbi_xi_step_hull {m : Nat} {A A' : Tm} (hy : WNF (.Xi m A)) (hy' : WNF (.Xi m A'))
    (hC : ∀ d, WNF d → Lt (.Xi m A) d → inC A' A' d = true)
    (hin : ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero)) :
    LBI (.Xi m A) (.Xi m A') := by
  have hA'F := hy'.xi.2.1
  refine lbi_xi_of hy hy' hin (fun E hE _ hlt hrel hA'E => ?_)
  have hEF := hE.xi.2.1
  have hA'C : inC A' E (.Xi m E) = true :=
    inC_mono A' A' (.Xi m E) E (.Xi m E) (hC _ hE hlt) (fun _ _ h => h)
      (fun v hv h => lt_transY (hA'F.of_mem_subs hv) hA'F hEF h hA'E)
  have hnle : ¬ Le (.Xi m E) (.Xi m A') := by
    intro hle
    rcases hle with e | hlt'
    · cases e; exact Lt.irrefl _ hA'E
    · rcases (lt_xi_xi0 (Lt.ne hA'E).symm).mp hlt' with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Lt.asymmY hA'F hEF hA'E h1
      · rw [hA'C] at h2; cases h2
  rcases hrel with hle | ⟨C, hCF, h1, h2⟩
  · exact hnle hle
  · rcases (lt_psi_xiY (π := .Xi m E) (a := C) (b := A') (n := m) rfl).mp h2 with hc | hb
    · exact hnle (le_of_ne_gtY hE hy' hc)
    · have hk : Lt (kTerm (m - 1)) (.Psi (.Xi m E) C) :=
        lt_transY (wnf_kTerm _) hy hCF (floorLev_lt_xi hy) h1
      rw [(baseOf_xi_iff m _ _).mpr ⟨hk, hC _ hCF h1⟩] at hb
      cases hb

/-- 前線による包：`x ∈ C(x, M_m)` で前線が全て `d` 未満なら `x ∈ C(x, d)` -/
theorem inC_self_of_fr {m : Nat} {x d : Tm} (hx : inC x x (.M m) = true)
    (hfr : ∀ f, f ∈ fr (.M m) x → Lt f d) : inC x x d = true :=
  inC_of_fr x hx (fun _ _ h => h) (fun f hf => inC_of_lt_node (fr_node hf) (hfr f hf))

/-- 種なしの近似の 1 段（包の形）：`x ≤ x'`（`R` 未満、`LBI x x'`）、`pre ⊕ x'` が `Ξ_m(pre ⊕ x)` より
大きい全ての `d` について `C(pre ⊕ x', d)` に入れば `LBI` -/
theorem lbi_app_step {m : Nat} {R x x' : Tm} {pre : List Tm} (hN : NFL (pre ++ [R]))
    (hx : WNF x) (hx' : WNF x') (hxx' : Le x x') (hx'R : Lt x' R) (hL : LBI x x')
    (hy : WNF (.Xi m (oadd (ofSummands pre) x))) (hy' : WNF (.Xi m (oadd (ofSummands pre) x')))
    (hA'S : Lt (oadd (ofSummands pre) x') (succM m))
    (hC : ∀ d, WNF d → Lt (.Xi m (oadd (ofSummands pre) x)) d →
      inC (oadd (ofSummands pre) x') (oadd (ofSummands pre) x') d = true) :
    LBI (.Xi m (oadd (ofSummands pre) x)) (.Xi m (oadd (ofSummands pre) x')) :=
  lbi_xi_step_hull hy hy' hC (fun E hE hAE hEA' _ =>
    xi_le_base_f0_of_lbi hy hy'.xi.2.1 hA'S (lbi_oadd_pre pre hN hx hx' hxx' hx'R hL) E hE hAE hEA')

end MahloOCF.FS
