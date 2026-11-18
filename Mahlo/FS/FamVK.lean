import Mahlo.FS.FamApp

/-! 族の閉包 `mahloVK m q qs Ξ_m(q) P` の場合分けと、`ω` 型の列の仕様 `FamNat`（`famNat_mahloVK`）。

* `q = 0`：`Ω` の塔（始点 `max(P, M_{m-1})`）。
* `q = q' + 1`：`q'` の `Ξ_m(q)` 以上の最後の加数 `R`（`M_m` 以上）で近似、なければ `Ξ_m(q')` の上の塔。
* `q` 極限：最後の加数で近似（`s0`）。種 `p` が `s0` の 0 番目以上なら、`p` より大きい最後の加数で
  近似（種を自然な和で足す）か、`p` の上の塔。種が大きい場合の、近似より後ろの族の評価は仮定
  `SeedHyp`（`T ≤ c < q` なら `Ξ_m(c) ≤ p`）で与える。 -/

namespace MahloOCF.FS

open Tm

/-! ### 加数の並びの分割 -/

theorem mem_takeWhile_imp' {α : Type} {f : α → Bool} : ∀ {l : List α} {a : α},
    a ∈ l.takeWhile f → f a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact hx
      · exact mem_takeWhile_imp' h
    · simp at h

theorem head_dropWhile_not' {α : Type} {f : α → Bool} : ∀ {l : List α} {d : α} {rest : List α},
    l.dropWhile f = d :: rest → f d = false
  | [], _, _, h => by cases h
  | x :: xs, d, rest, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact head_dropWhile_not' h
    · rename_i hx
      cases h
      simpa using hx

/-- `takeWhile` の最後の元で分ける -/
theorem dl_split {α : Type} {l : List α} {f : α → Bool} {a : α}
    (h : (l.takeWhile f).getLast? = some a) :
    l = (l.takeWhile f).dropLast ++ a :: l.dropWhile f ∧ f a = true ∧
      ∀ x rest', l.dropWhile f = x :: rest' → f x = false := by
  refine ⟨?_, mem_takeWhile_imp' (List.mem_of_getLast? h), fun x rest' e => head_dropWhile_not' e⟩
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp h
  have e1 : (l.takeWhile f).dropLast = l' := by rw [hl', List.dropLast_concat]
  rw [e1]
  have e2 := List.takeWhile_append_dropWhile (p := f) (l := l)
  rw [hl'] at e2
  calc l = l' ++ [a] ++ l.dropWhile f := e2.symm
    _ = l' ++ a :: l.dropWhile f := by simp

/-- 大きい順の加数の並びで、`x` の後ろの元は `x` 以下 -/
theorem le_of_after {L : List Tm} {x u : Tm} {rest : List Tm} (hN : NFL (L ++ x :: rest))
    (hu : u ∈ x :: rest) : Le u x := by
  have hN' : NFL (x :: rest) := nfl_append_right hN
  rcases List.mem_cons.mp hu with rfl | hu'
  · exact Or.inl rfl
  · exact le_of_ne_gtY (hN'.1 u (List.mem_cons_of_mem _ hu')).1 (hN'.1 x List.mem_cons_self).1
      (le_head_of_nfl hN' u hu')

/-- `splitGtD` の仕様：`summands q = pre ++ R :: rest`、`th < R`、`rest` の加数は `th` 以下 -/
theorem splitGtD_spec {th q : Tm} (hq : WNF q) (hth : WNF th) {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitGtD th (info q).sums = some (pre, R, r)) :
    ∃ rest, summands q = pre ++ R :: rest ∧ r = (info R).seq ∧ Lt th R ∧ ∀ u, u ∈ rest → Le u th := by
  unfold splitGtD at h
  split at h
  · cases h
  · rename_i hl
    cases h
    obtain ⟨e, hf, hd⟩ := dl_split hl
    have hmem : (R, r) ∈ (info q).sums := by rw [e]; simp
    have hs : summands q = ((info q).sums.takeWhile fun s => ltB th s.1).dropLast.map Prod.fst ++
        R :: ((info q).sums.dropWhile fun s => ltB th s.1).map Prod.fst := by
      rw [← info_sums_fst q]
      have := congrArg (List.map Prod.fst) e
      rw [this]
      simp
    refine ⟨_, hs, coh_sums q _ hmem, ltB_iff.mp hf, fun u hu => ?_⟩
    have hN := nfl_summands hq
    cases hdw : (info q).sums.dropWhile (fun s => ltB th s.1) with
    | nil => rw [hdw] at hu; cases hu
    | cons x rest' =>
      have hfx : ltB th x.1 = false := hd x rest' hdw
      rw [hdw] at hu hs
      rw [hs] at hN
      have hN2 : NFL ((((info q).sums.takeWhile fun s => ltB th s.1).dropLast.map Prod.fst ++ [R]) ++
          x.1 :: rest'.map Prod.fst) := by simpa using hN
      have hux := le_of_after hN2 hu
      have hxF := ((nfl_append_right hN2).1 x.1 List.mem_cons_self).1
      have huF := ((nfl_append_right hN2).1 u hu).1
      have hx' : ¬ Lt th x.1 := fun h' => by rw [ltB_iff.mpr h'] at hfx; cases hfx
      exact le_transY huF hxF hth hux (le_of_not_ltY hth hxF hx')

/-- `splitPosD` の仕様（`q` の最後の加数を除いた並びで）：`τ ≤ R`、`rest` の加数は `τ` 未満 -/
theorem splitPosD_spec {τ q : Tm} (hq : WNF q) (hτ : WNF τ) {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitPosD τ (info q).sums.dropLast = some (pre, R, r)) :
    ∃ rest, (summands q).dropLast = pre ++ R :: rest ∧ r = (info R).seq ∧ Le τ R ∧
      ∀ u, u ∈ rest → Lt u τ := by
  unfold splitPosD at h
  split at h
  · cases h
  · rename_i hl
    cases h
    obtain ⟨l, hl_def⟩ : ∃ l, l = (info q).sums.dropLast := ⟨_, rfl⟩
    rw [← hl_def] at hl ⊢
    obtain ⟨e, hf, hd⟩ := dl_split hl
    have hsub : ∀ x, x ∈ l → x ∈ (info q).sums := fun x hx => by
      rw [hl_def] at hx; exact (List.dropLast_sublist _).subset hx
    have hmem : (R, r) ∈ l := by rw [e]; simp
    have hlf : l.map Prod.fst = (summands q).dropLast := by
      rw [hl_def, List.map_dropLast, info_sums_fst]
    have hNd : NFL ((summands q).dropLast) := by
      cases hg : (summands q).getLast? with
      | none => rw [List.getLast?_eq_none_iff.mp hg]; exact ⟨by simp, trivial⟩
      | some z =>
        have e3 : summands q = (summands q).dropLast ++ [z] := by obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.mp hg; rw [hl0, List.dropLast_concat]
        have := nfl_summands hq
        rw [e3] at this
        exact nfl_append_left this
    have hs : (summands q).dropLast = (l.takeWhile fun s => leB τ s.1).dropLast.map Prod.fst ++
        R :: (l.dropWhile fun s => leB τ s.1).map Prod.fst := by
      rw [← hlf]
      have := congrArg (List.map Prod.fst) e
      rw [this]
      simp
    have hRF : WNF R := (hNd.1 R (by rw [hs]; simp)).1
    refine ⟨_, hs, coh_sums q _ (hsub _ hmem), le_of_ne_gtY hτ hRF (leB_iff.mp hf), fun u hu => ?_⟩
    cases hdw : l.dropWhile (fun s => leB τ s.1) with
    | nil => rw [hdw] at hu; cases hu
    | cons x rest' =>
      have hfx : leB τ x.1 = false := hd x rest' hdw
      rw [hdw] at hu hs
      have hN := hNd
      rw [hs] at hN
      have hN2 : NFL (((l.takeWhile fun s => leB τ s.1).dropLast.map Prod.fst ++ [R]) ++
          x.1 :: rest'.map Prod.fst) := by simpa using hN
      have hux := le_of_after hN2 hu
      have hxF := ((nfl_append_right hN2).1 x.1 List.mem_cons_self).1
      have huF := ((nfl_append_right hN2).1 u hu).1
      exact lt_of_le_of_ltY huF hxF hτ hux (lt_of_leB_false hτ hxF hfx)

/-- `splitPosD` が `none` なら、最後の加数を除いた加数は全て `τ` 未満 -/
theorem splitPosD_none {τ q : Tm} (hq : WNF q) (hτ : WNF τ)
    (h : splitPosD τ (info q).sums.dropLast = none) : ∀ u, u ∈ (summands q).dropLast → Lt u τ := by
  unfold splitPosD at h
  split at h
  · rename_i hl
    have htw := List.getLast?_eq_none_iff.mp hl
    have hlf : ((info q).sums.dropLast).map Prod.fst = (summands q).dropLast := by
      rw [List.map_dropLast, info_sums_fst]
    have hNd : NFL ((summands q).dropLast) := by
      cases hg : (summands q).getLast? with
      | none => rw [List.getLast?_eq_none_iff.mp hg]; exact ⟨by simp, trivial⟩
      | some z =>
        obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.mp hg
        have := nfl_summands hq
        rw [hl0] at this ⊢
        rw [List.dropLast_concat]
        exact nfl_append_left this
    intro u hu
    cases hd : (info q).sums.dropLast with
    | nil => rw [← hlf, hd] at hu; cases hu
    | cons x xs =>
      rw [hd, List.takeWhile_cons] at htw
      have hfx : leB τ x.1 = false := by
        cases e : leB τ x.1 with
        | false => rfl
        | true => rw [e] at htw; simp at htw
      rw [← hlf, hd] at hu hNd
      have hN : NFL ([] ++ x.1 :: xs.map Prod.fst) := by simpa using hNd
      have hux := le_of_after hN hu
      have hxF := ((nfl_append_right hN).1 x.1 List.mem_cons_self).1
      have huF := ((nfl_append_right hN).1 u hu).1
      exact lt_of_le_of_ltY huF hxF hτ hux (lt_of_leB_false hτ hxF hfx)
  · cases h

/-- 加数が `L ++ l'` の `c` が `q`（加数 `L ++ rest`）未満なら、`l'` の元は `rest` のある元以下 -/
theorem tail_le_of_lt {c q : Tm} {L l' rest : List Tm} (hc : WNF c) (hq : WNF q)
    (hsc : summands c = L ++ l') (hsq : summands q = L ++ rest) (hlt : Lt c q) :
    ∀ u, u ∈ l' → ∃ v, v ∈ rest ∧ Le u v := by
  have h1 : cmpList l' rest = .lt := by
    have := hlt; unfold Lt at this; rw [cmp_eq, hsc, hsq, cmpList_append_same] at this; exact this
  have hN : NFL (L ++ l') := by rw [← hsc]; exact nfl_summands hc
  have hNq : NFL (L ++ rest) := by rw [← hsq]; exact nfl_summands hq
  intro u hu
  cases l' with
  | nil => cases hu
  | cons x xs =>
    cases rest with
    | nil => rw [cmpList_cons_nil] at h1; cases h1
    | cons y ys =>
      refine ⟨y, List.mem_cons_self, ?_⟩
      have hx := (nfl_append_right hN).1 x List.mem_cons_self
      have hy := (nfl_append_right hNq).1 y List.mem_cons_self
      have hxy : Le x y := by
        rcases hcp : cmpP x y with _ | _ | _
        · exact Or.inr ((lt_principal_iff hx.2 hy.2).mpr hcp)
        · exact Or.inl (eq_of_cmpP_eqY hx.1 hy.1 hx.2 hy.2 hcp)
        · rw [cmpList_cons_cons_ne _ _ (by rw [hcp]; decide), hcp] at h1; cases h1
      exact le_transY ((nfl_append_right hN).1 u hu).1 hx.1 hy.1 (le_of_after hN hu) hxy

/-- 主要項の加数が全て `y` 未満なら全体も `y` 未満 -/
theorem lt_of_summands_lt {x y : Tm} (hx : WNF x) (hyp : isPrincipal y = true)
    (h : ∀ u, u ∈ summands x → Lt u y) : Lt x y := by
  cases hs : summands x with
  | nil => rw [eq_zero_of_summands_nil hs]; exact zero_lt (by intro e; rw [e] at hyp; cases hyp)
  | cons u r =>
    have hu := summands_WNF x hx u (by rw [hs]; exact List.mem_cons_self)
    exact lt_of_head_lt hyp hs ((lt_principal_iff hu.2 hyp).mp (h u (by rw [hs]; exact List.mem_cons_self)))

/-! ### 正則項の位置 -/

/-- `M_m ≤ σ ≤ M_m⁺` の正則項は `M_m` か `M_m⁺` -/
theorem reg_between_M {m : Nat} {σ : Tm} (hm : 1 ≤ m) (hσ : WNF σ) (hreg : IsRegY σ)
    (h1 : ¬ Lt σ (.M m)) (h2 : Le σ (succM m)) : σ = .M m ∨ σ = succM m := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  rcases h2 with e | h2
  · exact Or.inr e
  rcases hreg with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h1
  · exfalso
    have hcF := hσ.om.1
    have h3 : Lt c (succT (.M m)) := lt_om_iffG.mp h2
    have h4 : Le c (.M m) := le_of_lt_succT hcF hMF h3
    have h5 : ¬ Lt (.M m) (.Om c) := fun h => not_lt_of_leY hcF hMF h4 ((lt_M_omY hm hσ).mp h)
    rcases triY hσ hMF with h7 | h7 | h7
    · exact h1 h7
    · cases h7
    · exact h5 h7
  · rcases Nat.lt_trichotomy n m with hl | rfl | hl
    · exact absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h1
    · exact Or.inl rfl
    · exfalso
      exact Lt.asymmY hσ hSF h2 (lt_of_lev_lt' (by simp only [lev, succM, one]; omega))
  · exfalso
    have hn := hσ.xi.1
    have hl1 : m + 1 ≤ n := by
      rcases Nat.lt_or_ge n (m + 1) with hl | hl
      · exact absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h1
      · exact hl
    have hl2 : n ≤ m + 1 := by
      have := lev_le_of_lt_gen h2
      simp only [lev, succM, one] at this
      omega
    have hn' : n = m + 1 := by omega
    subst hn'
    have hOF : IsOF (.Xi (m + 1) p) := Or.inl ⟨_, _, rfl⟩
    have hMx : Lt (.M m) (.Xi (m + 1) p) := bot_ltY rfl (by simp only [lev]; omega) rfl rfl hσ
    have hpl : WNF (.plus (.M m) one) := succT_WNF hMF
    have h3 : Lt (.plus (.M m) one) (.Xi (m + 1) p) := (lt_plus_prin_iffY hpl rfl).mpr hMx
    exact Lt.asymmY hσ hSF h2 ((lt_om_OFG hOF hσ).mpr h3)

/-- 共終数が `Ξ_m(q)` 以上の `R`（`q` の加数）の共終数は `M_m` 以上 -/
theorem cof_ge_M {m : Nat} {q R σ : Tm} (hρ : WNF (.Xi m q)) (hRq : R ∈ summands q)
    (hRi : BigInv R σ) (hσρ : ¬ Lt σ (.Xi m q)) : ¬ Lt σ (.M m) := by
  have hqF := hρ.xi.2.1
  have hRC : inC R q (.Xi m q) = true := inC_of_mem_summands hqF (xi_selfY hρ) hRq
  have hσC := hRi.σC q _ (Cut.of_wnf hρ) hRC
  exact fun h => hσρ (coll_xi0 hρ σ hRi.props.σF hσC h)

/-! ### `q' = q - 1` -/

theorem xi_pred_wnf {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true) :
    WNF (.Xi m (predT q)) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hpF := predT_WNF hqF hs
  have hpq := lt_predT hqF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  refine WNF.mk_xi hm hpF (ne_gt_of_le (Or.inr (lt_of_lt_of_leY hpF hqF (WNF.succM hm) hpq
    (le_of_ne_gtY hqF (WNF.succM hm) hle)))) ((inC_iff_summandsW hpF).mpr (fun s hs' => ?_))
  rw [summands_predT hqF hys] at hs'
  have hsq : s ∈ summands q := by rw [hys]; exact List.mem_append_left _ hs'
  have hsF := (summands_WNF q hqF s hsq).1
  refine inC_mono_node s q _ _ _ (inC_of_mem_summands hqF hqC hsq) (fun _ _ _ h => h)
    (fun v hv hvs hvq => lt_pred_of_lt_succ hqF hs (hsF.of_mem_subs hv) hvq (fun e => ?_))
  have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands
    (show s ∈ summands (predT q) by rw [summands_predT hqF hys]; exact hs'))
  rw [e] at hvs
  omega

theorem xi_pred_lt {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true) :
    Lt (.Xi m (predT q)) (.Xi m q) := by
  have hqF := hρ.xi.2.1
  have hpF := predT_WNF hqF hs
  have hpq := lt_predT hqF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  refine (lt_xi_xi0 (Lt.ne hpq)).mpr (Or.inl ⟨hpq, (inC_iff_summandsW hpF).mpr (fun u hu => ?_)⟩)
  rw [summands_predT hqF hys] at hu
  exact inC_of_mem_summands hqF (xi_selfY hρ) (by rw [hys]; exact List.mem_append_left _ hu)

/-! ### 種 -/

theorem maxO_spec {P : Option Tm} {x : Tm} (hx : WNF x) (hP : ∀ p, P = some p → WNF p) :
    WNF (maxO P x) ∧ Le x (maxO P x) ∧ (∀ p, P = some p → Le p (maxO P x)) ∧
      (maxO P x = x ∨ ∃ p, P = some p ∧ maxO P x = p) := by
  cases P with
  | none => exact ⟨hx, Or.inl rfl, (fun _ hp => nomatch hp), Or.inl rfl⟩
  | some p =>
    have hpF := hP p rfl
    cases e : ltB p x with
    | true =>
      have h : maxO (some p) x = x := by simp [maxO, e]
      rw [h]
      refine ⟨hx, Or.inl rfl, (fun p' hp' => ?_), Or.inl rfl⟩
      cases hp'
      exact Or.inr (ltB_iff.mp e)
    | false =>
      have h : maxO (some p) x = p := by simp [maxO, e]
      rw [h]
      refine ⟨hpF, ?_, (fun p' hp' => ?_), Or.inr ⟨p, rfl, rfl⟩⟩
      · exact le_of_not_ltY hpF hx (fun h' => by rw [ltB_iff.mpr h'] at e; cases e)
      · cases hp'
        exact Or.inl rfl

/-- 種 `p` が大きいときの、近似より後ろの族の評価：`q` の加数を `L₁ ++ L₂`（`L₂` は `p` 以下）と
    分けたとき、`ofSummands L₁ ≤ c < q` なら `Ξ_m(c) ≤ p` -/
def SeedHyp (m : Nat) (q p : Tm) : Prop :=
  ∀ L₁ L₂, summands q = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
    ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q → ¬ Lt c (ofSummands L₁) → Le (.Xi m c) p

/-- `mkApp` は `Ξ` の生成では種が `R` 未満なら `app` -/
theorem mkApp_xi {ceil R P c : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (h : ltB P R = true) :
    mkApp ceil (.xi m) pre R r P c = some (.app ceil (.xi m) pre R r P c) := by
  simp [mkApp, h, Gen.tgt?]

/-- `app`（`Ξ` の生成）の 0 番目は `Ξ_m(·)` の形 -/
theorem app_xi_first {τ R P c : Tm} {m : Nat} {pre : List Tm} {r : SeqD} :
    ∃ A, (SeqD.app τ (.xi m) pre R r P c).first = .Xi m A := by
  unfold SeqD.first
  cases hr : r.dom with
  | big σ =>
    cases hl : ltB σ τ with
    | true => simp only [SeqD.dom, hr, hl, ↓reduceIte, SeqD.big, Gen.ap]; exact ⟨_, rfl⟩
    | false =>
      simp only [SeqD.dom, hr, hl, Bool.false_eq_true, ↓reduceIte, SeqD.nat, Gen.ap]; exact ⟨_, rfl⟩
  | _ => simp only [SeqD.dom, hr, SeqD.nat, Gen.ap]; exact ⟨_, rfl⟩

/-- 階 `m` の主要項は `M_{m-1}` 以上 -/
theorem floorLev_le_of_lev {m : Nat} {p : Tm} (hp : WNF p) (hpp : isPrincipal p = true)
    (hl : lev p = m) (hm : 1 ≤ m) : Le (floorLev m) p := by
  unfold floorLev kTerm
  split
  · exact zero_le _
  · rename_i hm1
    cases p with
    | zero => cases hpp
    | plus _ _ => cases hpp
    | M j =>
      simp only [lev] at hl
      have : j = m - 1 := by omega
      rw [this]; exact Or.inl rfl
    | _ => exact Or.inr (bot_ltY rfl (by simp only [lev] at hl ⊢; omega) hpp rfl hp)

/-- `1 < Ξ_m(q)` -/
theorem one_lt_xi {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) : Lt one (.Xi m q) :=
  lt_transY WNF.one WNF.om_zero hρ (lt_psi_targetY WNF.one)
    ((lt_om_OFG (Or.inl ⟨m, q, rfl⟩) hρ).mpr (zero_lt (by intro e; cases e)))

/-- `splitGtD` が `none` なら、加数は全て `th` 以下 -/
theorem splitGtD_none {th q : Tm} (hq : WNF q) (hth : WNF th)
    (h : splitGtD th (info q).sums = none) : ∀ u, u ∈ summands q → Le u th := by
  unfold splitGtD at h
  split at h
  · rename_i hl
    have htw := List.getLast?_eq_none_iff.mp hl
    intro u hu
    rw [← info_sums_fst q] at hu
    cases hd : (info q).sums with
    | nil => rw [hd] at hu; cases hu
    | cons x xs =>
      rw [hd, List.takeWhile_cons] at htw
      have hfx : ltB th x.1 = false := by
        cases e : ltB th x.1 with
        | false => rfl
        | true => rw [e] at htw; simp at htw
      rw [hd] at hu
      have hN : NFL ([] ++ x.1 :: xs.map Prod.fst) := by
        have := nfl_summands hq
        rw [← info_sums_fst q, hd] at this
        simpa using this
      have hux := le_of_after hN hu
      have hxF := ((nfl_append_right hN).1 x.1 List.mem_cons_self).1
      have huF := ((nfl_append_right hN).1 u hu).1
      have hx' : ¬ Lt th x.1 := fun h' => by rw [ltB_iff.mpr h'] at hfx; cases hfx
      exact le_transY huF hxF hth hux (le_of_not_ltY hth hxF hx')
  · cases h

/-- `R`（`q` の加数）の共終数が `Ξ_m(q)` 以上なら `M_m` か `M_m⁺`（後者なら `q = R = M_m⁺`） -/
theorem cof_split {m : Nat} {q R σ : Tm} (hρ : WNF (.Xi m q)) (hRq : R ∈ summands q)
    (hRi : BigInv R σ) (hσρ : ¬ Lt σ (.Xi m q)) :
    σ = .M m ∨ (σ = succM m ∧ R = succM m ∧ q = succM m) := by
  obtain ⟨hm, hqF, hle, -⟩ := hρ.xi
  have hSF := WNF.succM hm
  have hRF := (summands_WNF q hqF R hRq).1
  have hσF := hRi.props.σF
  have hqS : Le q (succM m) := le_of_ne_gtY hqF hSF hle
  have hRqle : Le R q := le_of_mem_summands hqF hRq
  have hσS : Le σ (succM m) := le_transY hσF hRF hSF hRi.σle (le_transY hRF hqF hSF hRqle hqS)
  rcases reg_between_M hm hσF hRi.σreg (cof_ge_M hρ hRq hRi hσρ) hσS with e | e
  · exact Or.inl e
  · refine Or.inr ⟨e, ?_, ?_⟩
    · rw [e] at hRi
      rcases hRi.σle with e' | h
      · exact e'.symm
      · exact absurd (lt_of_lt_of_leY hSF hRF hSF h (le_transY hRF hqF hSF hRqle hqS)) (Lt.irrefl _)
    · rw [e] at hRi
      have hSR : Le (succM m) q := le_transY hSF hRF hqF hRi.σle hRqle
      rcases hqS with e' | h
      · exact e'
      · exact absurd h (not_lt_of_leY hSF hqF hSR)

/-- 加数 `R`（`summands q = pre ++ R :: rest`）での近似 `app` の族の列（`R` の共終数で場合分け） -/
theorem famNat_app_split {m : Nat} {q P' R : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (hRi : Inv R) (hR1 : ¬ isSucc R = true)
    (hdom : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).dom = .omega)
    (hPρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) → Le (.Xi m c) P')
    (hseed : ∀ p, P = some p →
      (WNF p ∧ Le p P') ∨ Lt p (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first) :
    FamNat m q P (fun n => (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat n) := by
  have hρ := G.ht
  have hm := G.hm
  have hMF := G.hMF
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hRF := G.hRF
  have hfirst : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first =
      (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat 0 := by
    unfold SeqD.first; rw [hdom]
  cases hdR : dom R with
  | zero =>
    exfalso
    exact G.hR0 ((dom_eq_zero_iff hRF).mp hdR)
  | one => exact absurd ((dom_eq_one_iff hRF).mp hdR) hR1
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    refine famNat_app_nat G hdR hRN hPρ hP'ub (fun c h1 h2 h3 h4 => Or.inl (hrest c h1 h2 h3 h4))
      (fun p hp => (hseed p hp).imp id (fun h => ?_))
    rw [hfirst, app_xi_nat hr G.hPF (hRN.props.nf 0)] at h
    exact h
  | big σ =>
    have hB := hRi.2 σ hdR
    have hr : (info R).seq.dom = .big σ := hdR
    by_cases hσρ : Lt σ (.Xi m q)
    · exfalso
      simp only [SeqD.dom, hr, ltB_iff.mpr hσρ, ↓reduceIte] at hdom
      cases hdom
    · rcases cof_split hρ G.hRq hB hσρ with e | ⟨e, eR, eq⟩
      · subst e
        have G0 : XG m q .zero pre rest R :=
          ⟨hρ, G.hsum, WNF.zero, zero_lt G.hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        refine famNat_app_M G0 hdR hB hτ G.hPF hPρ hP'ub
          (fun c h1 h2 h3 h4 => Or.inl (hrest c h1 h2 h3 h4))
          (fun p hp => (hseed p hp).imp id (fun h => ?_))
        rw [hfirst, app_xi_M_nat hr hτ, gam_xi_M_succ, gam_xi_M_zero] at h
        change Lt p (.Xi m (combine (.xi m) pre .zero .zero (fundBig R P'))) at h
        rw [combine_xi m pre WNF.zero (hB.props.nf P' G.hPF (lt_transY G.hPF hρ hMF hPρ hρM))] at h
        exact h
      · subst eq
        subst eR
        have hsum := G.hsum
        have e1 : summands (succM m) = [succM m] := rfl
        rw [e1] at hsum
        have hpre : pre = [] := by
          cases pre with
          | nil => rfl
          | cons a l => simp at hsum
        subst hpre
        have hrest0 : rest = [] := by simpa using hsum
        subst hrest0
        refine famNat_app_S G hPρ hP'ub (fun p hp => (hseed p hp).imp id (fun h => ?_))
        rw [hfirst, app_xi_out_nat (succM_ne_M m) (succM_ne_xi m) (by rw [info_seq_succM]; rfl)
          (by cases e' : ltB (succM m) (.Xi m (succM m)) with
            | false => rfl
            | true => exact absurd (ltB_iff.mp e') (Lt.asymmY hρ (WNF.succM hm)
                (lt_transY hρ hMF (WNF.succM hm) hρM (M_lt_succM hm)))),
          gam_xi_S hm, info_seq_succM] at h
        rw [← combine_xi m [] G.hPF (virtE_F hm 0)]
        exact h

/-- 主要項 `p` より大きい主要項は後者でない（`1` でない） -/
theorem not_succ_of_gt {p R : Tm} (hpF : WNF p) (hpp : isPrincipal p = true) (hRp : isPrincipal R = true)
    (hRF : WNF R) (h : Lt p R) : ¬ isSucc R = true := by
  intro hs
  rw [isSucc_principal hRp] at hs
  have e : R = one := beq_iff_eq.mp hs
  rw [e] at h
  have hp0 : p ≠ .zero := by intro e'; rw [e'] at hpp; cases hpp
  exact not_lt_of_leY WNF.one hpF (one_leY hpF hp0) h

/-! ### `q = 0` -/

theorem famNat_vk_zero {m : Nat} {P : Option Tm} (hρ : WNF (.Xi m .zero))
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m .zero) ∧ isPrincipal p = true) :
    FamNat m .zero P (fun n => (mahloVK m .zero (info .zero).sums (.Xi m .zero) P).nat n) := by
  have hfl : WNF (floorLev m) := wnf_kTerm (m - 1)
  obtain ⟨hsF, hxs, hPs, hcase⟩ := maxO_spec (P := P) hfl (fun p hp => (hP p hp).1)
  have e : mahloVK m .zero (info .zero).sums (.Xi m .zero) P = .tower (maxO P (floorLev m)) := by
    unfold mahloVK; rw [ite_eq_left rfl]
  rw [e]
  show FamNat m .zero P (fun n => tower (maxO P (floorLev m)) (n + 1))
  refine famNat_tower hρ hsF ?_ hxs (fun p hp => ⟨(hP p hp).1, hPs p hp⟩)
    (fun c _ _ hc => absurd hc (not_lt_zero _)) (fun g d _ _ _ _ _ hPC => ?_)
  · rcases hcase with e' | ⟨p, hp, e'⟩
    · rw [e']; exact floorLev_lt_xi hρ
    · rw [e']; exact (hP p hp).2.1
  · rcases hcase with e' | ⟨p, hp, e'⟩
    · rw [e']; exact inC_kTerm _ _ _
    · rw [e']; exact hPC p hp

/-! ### `q = q' + 1` -/

theorem famNat_vk_succ {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true)
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega) :
    FamNat m q P (fun n => (mahloVK m q (info q).sums (.Xi m q) P).nat n) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hq0 : q ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hpF := predT_WNF hqF hs
  have hpq := lt_predT hqF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hsp : summands (predT q) = ys := summands_predT hqF hys
  have hdl : (summands q).dropLast = ys := by rw [hys, List.dropLast_concat]
  have hyF := xi_pred_wnf hρ hs
  have hyρ := xi_pred_lt hρ hs
  obtain ⟨s, hs_def⟩ : ∃ s, s = maxO P (.Xi m (predT q)) := ⟨_, rfl⟩
  obtain ⟨hsF, hys', hPs, hcase⟩ := maxO_spec (P := P) hyF (fun p hp => (hP p hp).1)
  rw [← hs_def] at hsF hys' hPs hcase
  have hsρ : Lt s (.Xi m q) := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; exact hyρ
    · rw [e]; exact (hP p hp).2.1
  have hsp' : isPrincipal s = true := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; rfl
    · rw [e]; exact (hP p hp).2.2
  have hsM : Lt s (.M m) := lt_transY hsF hρ hMF hsρ hρM
  -- `s` の所属
  have hsC : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC s g d = true := by
    intro g d hg _ _ hρC hρd hPC
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]
      rcases inC_xi_iff.mp hρC with h1 | ⟨hqC', hqg⟩
      · exact absurd h1 hρd
      refine inC_xi_iff.mpr (Or.inr ⟨(inC_iff_summandsW hpF).mpr (fun u hu => ?_),
        lt_transY hpF hqF hg hpq hqg⟩)
      rw [hsp] at hu
      exact inC_of_mem_summands hqF hqC' (by rw [hys]; exact List.mem_append_left _ hu)
    · rw [e]; exact hPC p hp
  -- `c ≤ q'` の族の元は `Ξ_m(q')` 以下
  have hcl : ∀ c, WNF (.Xi m c) → Lt c q →
      (Lt c (predT q) → inC c (predT q) (.Xi m (predT q)) = true) → Le (.Xi m c) s := by
    intro c hc hcq hcC
    have hcF := hc.xi.2.1
    refine le_transY hc hyF hsF ?_ hys'
    rcases le_pred_of_lt_succ hqF hs hcF hcq with e | hlt
    · rw [e]; exact Or.inl rfl
    · exact Or.inr ((lt_xi_xi0 (Lt.ne hlt)).mpr (Or.inl ⟨hlt, hcC hlt⟩))
  have hpred : pred q = predT q := rfl
  unfold mahloVK at hdom ⊢
  rw [ite_eq_right hq0, ite_eq_left hs] at hdom ⊢
  simp only [hpred, ← hs_def] at hdom ⊢
  cases hsplit : splitPosD (.Xi m q) (info q).sums.dropLast with
  | none =>
    simp only [hsplit] at hdom ⊢
    -- `q' < Ξ_m(q)`：`Ξ_m(q')` の上の塔
    have hall := splitPosD_none hqF hρ hsplit
    have hpρ : Lt (predT q) (.Xi m q) :=
      lt_of_summands_lt hpF rfl (fun u hu => hall u (by rw [hdl, ← hsp]; exact hu))
    have hpM := lt_transY hpF hρ hMF hpρ hρM
    have hpy : Lt (predT q) (.Xi m (predT q)) := lt_xi_self hyF hpM
    show FamNat m q P (fun n => tower s (n + 1))
    exact famNat_tower hρ hsF hsρ (le_transY (wnf_kTerm _) hyF hsF (Or.inr (floorLev_lt_xi hyF)) hys')
      (fun p hp => ⟨(hP p hp).1, hPs p hp⟩)
      (fun c hc _ hcq => hcl c hc hcq (fun hlt => inC_of_lt_cut (Cut.of_wnf hyF) _ hc.xi.2.1
        (lt_transY hc.xi.2.1 hpF hyF hlt hpy))) hsC
  | some val =>
    obtain ⟨pre, R, r⟩ := val
    obtain ⟨rest, hsd, hr, hρR, hrest⟩ := splitPosD_spec hqF hρ hsplit
    subst hr
    have hsq : summands q = pre ++ R :: (rest ++ [one]) := by
      rw [hys, ← hdl, hsd]; simp
    have hRq : R ∈ summands q := by rw [hsq]; simp
    have hRW := summands_WNF q hqF R hRq
    have hsR : Lt s R := lt_of_lt_of_leY hsF hρ hRW.1 hsρ hρR
    simp only [hsplit, mkApp_xi (ltB_iff.mpr hsR)] at hdom ⊢
    have hRi := hRinv R hRq
    have G : XG m q s pre (rest ++ [one]) R :=
      ⟨hρ, hsq, hsF, hsR, hsM, Or.inr hsp'⟩
    -- `T ≤ c < q` の族の元は `Ξ_m(q')` 以下
    have hrest' : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
        ¬ Lt c (ofSummands (pre ++ [R])) → Le (.Xi m c) s := by
      intro c hc _ hcq hcT
      have hcF := hc.xi.2.1
      refine hcl c hc hcq (fun hlt => ?_)
      have hTq : Lt c q := hcq
      have h1 : cmpList (summands c) (pre ++ [R]) ≠ .lt := by
        intro h; apply hcT; unfold Lt; rw [cmp_eq, G.hsT]; exact h
      have h2 : cmpList (summands c) (pre ++ R :: (rest ++ [one])) = .lt := by
        have := hTq; unfold Lt at this; rw [cmp_eq, hsq] at this; exact this
      obtain ⟨l', hl'⟩ := prefix_of_between pre R (rest ++ [one]) (summands c) G.hN.1
        (nfl_summands hcF).1 h1 h2
      have hpsum : summands (predT q) = pre ++ R :: rest := by rw [hsp, ← hdl, hsd]
      have hcp : summands c = (pre ++ [R]) ++ l' := by rw [hl']; simp
      have hpp : summands (predT q) = (pre ++ [R]) ++ rest := by rw [hpsum]; simp
      have htl := tail_le_of_lt hcF hpF hcp hpp hlt
      refine (inC_iff_summandsW hcF).mpr (fun u hu => ?_)
      rw [hcp] at hu
      rcases List.mem_append.mp hu with hu | hu
      · exact inC_of_mem_summands hpF (xi_selfY hyF) (by rw [hpp]; exact List.mem_append_left _ hu)
      · obtain ⟨v, hv, huv⟩ := htl u hu
        have hvp : v ∈ summands (predT q) := by rw [hpp]; exact List.mem_append_right _ hv
        have hvF := (summands_WNF _ hpF v hvp).1
        have huF := (summands_WNF c hcF u (by rw [hcp]; exact List.mem_append_right _ hu)).1
        have hvy : Lt v (.Xi m (predT q)) := coll_xi0 hyF v hvF
          (inC_of_mem_summands hpF (xi_selfY hyF) hvp) (lt_transY hvF hρ hMF (hrest v hv) hρM)
        exact inC_of_lt_cut (Cut.of_wnf hyF) _ huF (lt_of_le_of_ltY huF hvF hyF huv hvy)
    cases hdR : dom R with
    | zero =>
      exfalso
      have := (dom_eq_zero_iff hRW.1).mp hdR
      rw [this] at hRW; cases hRW.2
    | one =>
      exfalso
      have h1 := (dom_eq_one_iff hRW.1).mp hdR
      rw [isSucc_principal hRW.2] at h1
      have h2 : R = one := beq_iff_eq.mp h1
      rw [h2] at hρR
      exact not_lt_of_leY hρ WNF.one hρR (one_lt_xi hρ)
    | omega =>
      exact famNat_app_nat G hdR (hRi.1 hdR) hsρ hsC
        (fun c h1 h2 h3 h4 => Or.inl (hrest' c h1 h2 h3 h4))
        (fun p hp => Or.inl ⟨(hP p hp).1, hPs p hp⟩)
    | big σ =>
      have hB := hRi.2 σ hdR
      have hσF := hB.props.σF
      have hSF := WNF.succM hm
      have hqS : Le q (succM m) := le_of_ne_gtY hqF hSF hle
      by_cases hσρ : Lt σ (.Xi m q)
      · exfalso
        have hr' : (info R).seq.dom = .big σ := hdR
        simp only [SeqD.dom, hr', ltB_iff.mpr hσρ, ↓reduceIte] at hdom
        cases hdom
      · have hσM := cof_ge_M hρ hRq hB hσρ
        have hσS : Le σ (succM m) := le_transY hσF hRW.1 hSF hB.σle
          (le_transY hRW.1 hqF hSF (le_of_mem_summands hqF hRq) hqS)
        rcases reg_between_M hm hσF hB.σreg hσM hσS with e | e
        · subst e
          have G0 : XG m q .zero pre (rest ++ [one]) R :=
            ⟨hρ, hsq, WNF.zero, zero_lt G.hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
          have hτ : ltB (.M m) (.Xi m q) = false := by
            cases e : ltB (.M m) (.Xi m q) with
            | false => rfl
            | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
          exact famNat_app_M G0 hdR hB hτ hsF hsρ hsC
            (fun c h1 h2 h3 h4 => Or.inl (hrest' c h1 h2 h3 h4))
            (fun p hp => Or.inl ⟨(hP p hp).1, hPs p hp⟩)
        · exfalso
          rw [e] at hB
          have hRp : Le R (predT q) :=
            le_of_mem_summands hpF (by rw [hsp, ← hdl, hsd]; simp)
          have h1 : Lt (succM m) q := lt_of_le_of_ltY hSF hpF hqF
            (le_transY hSF hRW.1 hpF hB.σle hRp) hpq
          exact not_lt_of_leY hqF hSF hqS h1

/-! ### `q` 極限 -/

theorem famNat_vk_lim {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hq0 : q ≠ .zero) (hs : ¬ isSucc q = true)
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hSeed : ∀ p, P = some p → ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first ≠ p → SeedHyp m q p)
    (hB5 : ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega) :
    FamNat m q P (fun n => (mahloVK m q (info q).sums (.Xi m q) P).nat n) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hne := summands_ne_nil hq0
  obtain ⟨R, hRdef⟩ : ∃ R, (summands q).getLast hne = R := ⟨_, rfl⟩
  have hpre : preT (info q).sums = (summands q).dropLast := preT_info q
  have hlast : lastT (info q).sums = R := by
    rw [lastT_info, List.getLast?_eq_some_getLast hne, hRdef]; rfl
  have hlastS : lastS (info q).sums = (info R).seq := by rw [lastS_coh (coh_sums q), hlast]
  have hsq : summands q = (summands q).dropLast ++ [R] := by
    rw [← hRdef]; exact (List.dropLast_concat_getLast hne).symm
  have hRq : R ∈ summands q := by rw [← hRdef]; exact List.getLast_mem hne
  have hRW := summands_WNF q hqF R hRq
  have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsq hRW.2]; exact hs
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hRi := hRinv R hRq
  have h0ρ : Lt .zero (.Xi m q) := zero_lt (by intro e; cases e)
  -- 最後の加数での近似では、後ろの族はない
  have hTq : ofSummands ((summands q).dropLast ++ [R]) = q := by
    rw [← hsq]; exact ofSummands_summands q hqF
  have hrest0 : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands ((summands q).dropLast ++ [R])) → Le (.Xi m c) .zero := by
    intro c _ _ hcq hcT
    rw [hTq] at hcT
    exact absurd hcq hcT
  unfold mahloVK at hdom ⊢
  rw [ite_eq_right hq0, ite_eq_right hs] at hdom ⊢
  simp only [hpre, hlast, hlastS] at hdom ⊢
  cases P with
  | none =>
    exact famNat_app_split G0 hRi hRns hdom h0ρ (fun _ _ _ _ _ _ _ _ => inC_zero _ _) hrest0
      (fun p hp => nomatch hp)
  | some p =>
    obtain ⟨hpF, hpρ, hpp⟩ := hP p rfl
    dsimp only at hdom ⊢
    by_cases h1 : ltB p (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first
      = true
    · rw [ite_eq_left h1] at hdom ⊢
      exact famNat_app_split G0 hRi hRns hdom h0ρ (fun _ _ _ _ _ _ _ _ => inC_zero _ _) hrest0
        (fun p' hp' => by cases hp'; exact Or.inr (ltB_iff.mp h1))
    rw [ite_eq_right h1] at hdom ⊢
    by_cases h2 : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first = p
    · -- 列を一つずらす
      rw [ite_eq_left h2] at hdom ⊢
      have hRd : dom R = .omega := by
        have := hB5 p rfl (by rw [hpre, hlast, hlastS]; exact h2)
        rwa [hlast] at this
      have hRN := hRi.1 hRd
      have hs0dom : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).dom =
          .omega := app_xi_dom_nat hRd
      have F0 := famNat_app_split (P := none) G0 hRi hRns hs0dom h0ρ
        (fun _ _ _ _ _ _ _ _ => inC_zero _ _) hrest0 (fun p hp => nomatch hp)
      have hr : (info R).seq.dom = .omega := hRd
      refine famNat_app_shift G0 hRd hRN h0ρ (fun _ _ _ _ _ _ _ _ => inC_zero _ _)
        (fun c _ _ hcq hcT => by rw [hTq] at hcT; exact absurd hcq hcT) (fun p' hp' => ?_)
      cases hp'
      have h3 : Lt ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat 0)
          ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat (0 + 1)) :=
        F0.mono 0
      have hfirst : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first =
          (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat 0 := by
        unfold SeqD.first; rw [hs0dom]
      rw [← hfirst, h2, app_xi_nat hr WNF.zero (hRN.props.nf 1)] at h3
      exact h3
    rw [ite_eq_right h2] at hdom ⊢
    have hSp : SeedHyp m q p :=
      hSeed p rfl (by rw [hpre, hlast, hlastS]; exact h1) (by rw [hpre, hlast, hlastS]; exact h2)
    cases hsg : splitGtD p (info q).sums with
    | none =>
      -- `p` の上の `Ω` の塔
      simp only [hsg] at hdom ⊢
      show FamNat m q (some p) (fun n => tower p (n + 1))
      have hall := splitGtD_none hqF hpF hsg
      obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := (summands q).dropLast) (R := R)
        (r := (info R).seq) (P := .zero) (c := .zero)
      have hlev : lev p = m := by
        have h4 : lev p ≤ m := by have := lev_le_of_lt_gen hpρ; simpa [lev] using this
        rcases Nat.lt_or_ge (lev p) m with h5 | h5
        · exfalso
          apply h1
          rw [hA]
          exact ltB_iff.mpr (lt_of_lev_lt' (by simp only [lev]; exact h5))
        · omega
      refine famNat_tower hρ hpF hpρ (floorLev_le_of_lev hpF hpp hlev hm)
        (fun p' hp' => by cases hp'; exact ⟨hpF, Or.inl rfl⟩)
        (fun c hc hcρ hcq => hSp [] (summands q) rfl hall c hc hcρ hcq (not_lt_zero c))
        (fun g d _ _ _ _ _ hPC => hPC p rfl)
    | some val =>
      obtain ⟨pre, R', r'⟩ := val
      obtain ⟨rest, hsq', hr', hpR', hrest'⟩ := splitGtD_spec hqF hpF hsg
      subst hr'
      have hR'q : R' ∈ summands q := by rw [hsq']; simp
      have hR'W := summands_WNF q hqF R' hR'q
      simp only [hsg, mkApp_xi (ltB_iff.mpr hpR')] at hdom ⊢
      have G : XG m q p pre rest R' :=
        ⟨hρ, hsq', hpF, hpR', lt_transY hpF hρ hMF hpρ hρM, Or.inr hpp⟩
      exact famNat_app_split G (hRinv R' hR'q) (not_succ_of_gt hpF hpp hR'W.2 hR'W.1 hpR') hdom hpρ
        (fun g d _ _ _ _ _ hPC => hPC p rfl)
        (fun c h1 h2 h3 h4 => hSp (pre ++ [R']) rest (by rw [hsq']; simp) hrest' c h1 h2 h3 h4)
        (fun p' hp' => by cases hp'; exact Or.inl ⟨hpF, Or.inl rfl⟩)

/-! ### まとめ -/

/-- 族の閉包 `mahloVK m q qs Ξ_m(q) P` の `ω` 型の列の仕様 -/
theorem famNat_mahloVK {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hSeed : ∀ p, P = some p → ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first ≠ p → SeedHyp m q p)
    (hB5 : ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega) :
    FamNat m q P (fun n => (mahloVK m q (info q).sums (.Xi m q) P).nat n) := by
  by_cases hq0 : q = .zero
  · subst hq0; exact famNat_vk_zero hρ hP
  by_cases hs : isSucc q = true
  · exact famNat_vk_succ hρ hs hRinv hP hdom
  · exact famNat_vk_lim hρ hq0 hs hRinv hP hSeed hB5 hdom

end MahloOCF.FS
