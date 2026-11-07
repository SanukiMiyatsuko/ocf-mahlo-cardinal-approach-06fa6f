import Mahlo.FS.Def
import Mahlo.WF.Wmax

/-! 基本列の定義に使う和・自然な和・倍の性質（標準形を保つこと、大小）。 -/

namespace MahloOCF.FS

open Tm

theorem ltB_iff {a b : Tm} : ltB a b = true ↔ Lt a b := by
  unfold ltB Lt; simp

theorem leB_iff {a b : Tm} : leB a b = true ↔ cmp a b ≠ .gt := by
  unfold leB; simp

/-! ### 大きい順の加数の列 -/

/-- 隣り合う加数が大きい順（後ろが前以下） -/
def Desc : List Tm → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => cmp y x ≠ .gt ∧ Desc (y :: rest)

/-- 標準形の主要項からなる大きい順の列 -/
def NFL (l : List Tm) : Prop := (∀ x, x ∈ l → WNF x ∧ isPrincipal x = true) ∧ Desc l

theorem summands_ofSummands : ∀ l : List Tm, (∀ x, x ∈ l → isPrincipal x = true) →
    summands (ofSummands l) = l
  | [], _ => rfl
  | [a], h => summands_principal (h a List.mem_cons_self)
  | a :: b :: rest, h => by
    show summands (plus a (ofSummands (b :: rest))) = a :: b :: rest
    rw [summands_plus, summands_ofSummands (b :: rest)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem ofSummands_ne_zero : ∀ {l : List Tm}, l ≠ [] → (∀ x, x ∈ l → isPrincipal x = true) →
    ofSummands l ≠ zero
  | [], h, _ => absurd rfl h
  | [a], _, hp => by
    intro e; have := hp a List.mem_cons_self; rw [show ofSummands [a] = a from rfl] at e
    rw [e] at this; cases this
  | _ :: _ :: _, _, _ => by intro e; cases e

theorem wnf_ofSummands : ∀ {l : List Tm}, NFL l → WNF (ofSummands l)
  | [], _ => WNF.zero
  | [a], h => (h.1 a List.mem_cons_self).1
  | a :: b :: rest, h => by
    have ha := h.1 a List.mem_cons_self
    have hrest : NFL (b :: rest) :=
      ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), h.2.2⟩
    have hp : ∀ x, x ∈ b :: rest → isPrincipal x = true := fun x hx => (hrest.1 x hx).2
    refine WNF.mk_plus ha.1 (wnf_ofSummands hrest) ha.2 (ofSummands_ne_zero (by simp) hp) ?_
    intro h' rest' hs
    rw [summands_ofSummands _ hp, List.cons.injEq] at hs
    rw [← hs.1]
    exact h.2.1

theorem nfl_summands : ∀ {t : Tm}, WNF t → NFL (summands t)
  | .zero, _ => ⟨by simp [summands], trivial⟩
  | .plus a b, h => by
    obtain ⟨ha, hb, hap, hb0⟩ := h.plus
    have ihb := nfl_summands hb
    refine ⟨summands_WNF _ h, ?_⟩
    rw [summands_plus]
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons h' rest =>
      rw [hs] at ihb
      exact ⟨h.plus_head hs, ihb.2⟩
  | .M _, h | .Om _, h | .Xi _ _, h | .Psi _ _, h => ⟨summands_WNF _ h, trivial⟩

theorem nfl_of_wnf_principal {x : Tm} (h : WNF x) (hp : isPrincipal x = true) : NFL [x] :=
  ⟨fun y hy => by rw [List.mem_singleton] at hy; rw [hy]; exact ⟨h, hp⟩, trivial⟩

/-- 列の比較 -/
theorem cmp_ofSummands {l m : List Tm} (hl : ∀ x, x ∈ l → isPrincipal x = true)
    (hm : ∀ x, x ∈ m → isPrincipal x = true) :
    cmp (ofSummands l) (ofSummands m) = cmpList l m := by
  rw [cmp_eq, summands_ofSummands l hl, summands_ofSummands m hm]

theorem nfl_tail {x : Tm} {l : List Tm} (h : NFL (x :: l)) : NFL l := by
  refine ⟨fun y hy => h.1 y (List.mem_cons_of_mem _ hy), ?_⟩
  cases l with
  | nil => trivial
  | cons y rest => exact h.2.2

theorem nfl_append_left {l m : List Tm} (h : NFL (l ++ m)) : NFL l := by
  induction l with
  | nil => exact ⟨by simp, trivial⟩
  | cons x xs ih =>
    have ht := ih (nfl_tail h)
    refine ⟨fun y hy => h.1 y (List.mem_append_left _ hy), ?_⟩
    cases xs with
    | nil => trivial
    | cons y rest => exact ⟨h.2.1, ht.2⟩

/-! ### 辞書式比較の補題 -/

theorem cmpList_append_same : ∀ (l m m' : List Tm), cmpList (l ++ m) (l ++ m') = cmpList m m'
  | [], _, _ => rfl
  | x :: xs, m, m' => by
    rw [List.cons_append, List.cons_append, cmpList_cons_cons_eq _ _ (cmpP_self x)]
    exact cmpList_append_same xs m m'

theorem cmpList_head_lt {x y : Tm} (xs ys : List Tm) (h : cmpP x y = .lt) :
    cmpList (x :: xs) (y :: ys) = .lt := by
  rw [cmpList_cons_cons_ne _ _ (by rw [h]; decide), h]

theorem desc_append : ∀ {l m : List Tm}, Desc l → Desc m →
    (∀ a b, l.getLast? = some a → m.head? = some b → cmp b a ≠ .gt) → Desc (l ++ m)
  | [], _, _, hm, _ => hm
  | [a], [], _, _, _ => trivial
  | [a], b :: rest, _, hm, hj => ⟨hj a b rfl rfl, hm⟩
  | a :: a' :: rest, m, hl, hm, hj => by
    refine ⟨hl.1, ?_⟩
    exact desc_append hl.2 hm (fun x y hx hy => hj x y (by simpa [List.getLast?_cons_cons] using hx) hy)

theorem nfl_append {l m : List Tm} (hl : NFL l) (hm : NFL m)
    (hj : ∀ a b, l.getLast? = some a → m.head? = some b → cmp b a ≠ .gt) : NFL (l ++ m) :=
  ⟨fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hl.1 x h
    · exact hm.1 x h, desc_append hl.2 hm.2 hj⟩

theorem nfl_takeWhile {l : List Tm} (p : Tm → Bool) (h : NFL l) : NFL (l.takeWhile p) := by
  have e := List.takeWhile_append_dropWhile (p := p) (l := l)
  rw [← e] at h
  exact nfl_append_left h

theorem mem_takeWhile_imp {p : Tm → Bool} : ∀ {l : List Tm} {a : Tm}, a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact hx
      · exact mem_takeWhile_imp h
    · simp at h

theorem takeWhile_getLast {l : List Tm} {p : Tm → Bool} {a : Tm}
    (h : (l.takeWhile p).getLast? = some a) : p a = true :=
  mem_takeWhile_imp (List.mem_of_getLast? h)

/-- 先頭が `x` 以下の大きい順の列 `S` に `x` を前置しても小さくならない -/
theorem cmpList_cons_ge : ∀ {S : List Tm} {x : Tm}, NFL S → WNF x → isPrincipal x = true →
    (∀ b, S.head? = some b → cmp b x ≠ .gt) → cmpList S (x :: S) ≠ .gt
  | [], _, _, _, _, _ => by rw [cmpList_nil_cons]; decide
  | s :: S', x, hS, hx, hxp, hh => by
    have hs := hS.1 s List.mem_cons_self
    have hsx : cmp s x ≠ .gt := hh s rfl
    rw [cmp_principal hs.2 hxp] at hsx
    cases e : cmpP s x with
    | lt => rw [cmpList_head_lt _ _ e]; decide
    | gt => exact absurd e hsx
    | eq =>
      have hsx' : s = x := eq_of_cmpP_eqY hs.1 hx hs.2 hxp e
      subst hsx'
      rw [cmpList_cons_cons_eq _ _ e]
      exact cmpList_cons_ge (nfl_tail hS) hs.1 hs.2 (fun b hb => by
        cases S' with
        | nil => cases hb
        | cons b' rest =>
          simp only [List.head?_cons, Option.some.injEq] at hb
          rw [← hb]; exact hS.2.1)

theorem nfl_append_right : ∀ {L S : List Tm}, NFL (L ++ S) → NFL S
  | [], _, h => h
  | _ :: L', _, h => nfl_append_right (L := L') (nfl_tail h)

theorem le_ofSummands_cons {x : Tm} {T : List Tm} (h : NFL (x :: T)) :
    Le (ofSummands T) (ofSummands (x :: T)) := by
  have hT := nfl_tail h
  have hx := h.1 x List.mem_cons_self
  apply le_of_ne_gtY (wnf_ofSummands hT) (wnf_ofSummands h)
  rw [cmp_ofSummands (fun y hy => (hT.1 y hy).2) (fun y hy => (h.1 y hy).2)]
  refine cmpList_cons_ge hT hx.1 hx.2 (fun b hb => ?_)
  cases T with
  | nil => cases hb
  | cons b' rest =>
    simp only [List.head?_cons, Option.some.injEq] at hb
    rw [← hb]; exact h.2.1

/-- 大きい順の列の前に要素を並べても小さくならない -/
theorem le_ofSummands_prepend : ∀ {L S : List Tm}, NFL (L ++ S) →
    Le (ofSummands S) (ofSummands (L ++ S))
  | [], _, _ => Le.refl _
  | x :: L', S, h => by
    have h' : NFL (L' ++ S) := nfl_tail h
    have hS : NFL S := nfl_append_right h'
    exact le_transY (wnf_ofSummands hS) (wnf_ofSummands h') (wnf_ofSummands h)
      (le_ofSummands_prepend h') (le_ofSummands_cons h)

theorem zero_le (t : Tm) : Le .zero t := by
  by_cases h : t = .zero
  · exact Or.inl h.symm
  · exact Or.inr (zero_lt h)

/-- 主要項 `z` 未満の標準形の先頭は `z` 未満 -/
theorem head_lt_prin {y z h : Tm} {r : List Tm} (hy : summands y = h :: r) (hzp : isPrincipal z = true)
    (hlt : Lt y z) : cmpP h z = .lt := by
  unfold Lt at hlt
  rw [cmp_eq, hy, summands_principal hzp] at hlt
  rcases cmpList_lt_cases hlt with e | ⟨-, e⟩
  · exact e
  · cases r <;> simp [cmpList_nil_nil, cmpList_cons_nil] at e

/-- 標準形 `y < y'` なら先頭も `y` ≤ `y'` -/
theorem head_le_of_lt {y y' h h' : Tm} {r r' : List Tm} (hy : summands y = h :: r)
    (hy' : summands y' = h' :: r') (hlt : Lt y y') : cmpP h h' ≠ .gt := by
  unfold Lt at hlt
  rw [cmp_eq, hy, hy'] at hlt
  rcases cmpList_lt_cases hlt with e | ⟨e, -⟩ <;> rw [e] <;> decide

theorem takeWhile_append_of_all {p : Tm → Bool} : ∀ {A : List Tm} (B : List Tm),
    (∀ a, a ∈ A → p a = true) → (A ++ B).takeWhile p = A ++ B.takeWhile p
  | [], _, _ => rfl
  | a :: A', B, h => by
    rw [List.cons_append, List.takeWhile_cons, ite_eq_left (h a List.mem_cons_self),
      takeWhile_append_of_all B (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem head_dropWhile_not {p : Tm → Bool} : ∀ {l : List Tm} {d : Tm} {rest : List Tm},
    l.dropWhile p = d :: rest → p d = false
  | [], _, _, h => by cases h
  | x :: xs, d, rest, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact head_dropWhile_not h
    · rename_i hx
      simp only [List.cons.injEq] at h
      rw [← h.1]; simpa using hx

theorem summands_oadd {x y h : Tm} {r : List Tm} (hy : summands y = h :: r)
    (hxp : ∀ s, s ∈ summands x → isPrincipal s = true) (hyp : ∀ s, s ∈ summands y → isPrincipal s = true) :
    summands (oadd x y) = (summands x).takeWhile (fun s => leB h s) ++ summands y := by
  have hp : ∀ s, s ∈ (summands x).takeWhile (fun s => leB h s) ++ summands y → isPrincipal s = true := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hxp s ((List.takeWhile_sublist _).subset hs)
    · exact hyp s hs
  unfold oadd
  rw [hy]
  simp only
  rw [← hy, summands_ofSummands _ hp]

theorem oadd_zero (x : Tm) : oadd x .zero = x := rfl

theorem wnf_oadd {x y : Tm} (hx : WNF x) (hy : WNF y) : WNF (oadd x y) := by
  cases hs : summands y with
  | nil =>
    have : y = .zero := by cases y <;> simp_all [summands]
    rw [this]; exact hx
  | cons h r =>
    unfold oadd
    rw [hs]
    simp only
    have hX := nfl_summands hx
    have hY := nfl_summands hy
    rw [hs] at hY
    refine wnf_ofSummands (nfl_append (nfl_takeWhile _ hX) hY (fun a b ha hb => ?_))
    simp only [List.head?_cons, Option.some.injEq] at hb
    rw [← hb]
    exact leB_iff.mp (takeWhile_getLast ha)

theorem le_oadd_right {x y : Tm} (hx : WNF x) (hy : WNF y) : Le y (oadd x y) := by
  cases hs : summands y with
  | nil =>
    have : y = .zero := by cases y <;> simp_all [summands]
    rw [this]; exact zero_le _
  | cons h r =>
    have hX := nfl_summands hx
    have hY := nfl_summands hy
    have e1 := ofSummands_summands y hy
    have hXp : ∀ s, s ∈ summands x → isPrincipal s = true := fun s hs => (hX.1 s hs).2
    have hYp : ∀ s, s ∈ summands y → isPrincipal s = true := fun s hs => (hY.1 s hs).2
    have e2 : oadd x y = ofSummands ((summands x).takeWhile (fun s => leB h s) ++ summands y) := by
      have := ofSummands_summands (oadd x y) (wnf_oadd hx hy)
      rw [summands_oadd hs hXp hYp] at this
      exact this.symm
    rw [e2]
    have hnfl : NFL ((summands x).takeWhile (fun s => leB h s) ++ summands y) := by
      have hY' := hY
      rw [hs] at hY' ⊢
      exact nfl_append (nfl_takeWhile _ hX) hY' (fun a b ha hb => by
        simp only [List.head?_cons, Option.some.injEq] at hb
        rw [← hb]; exact leB_iff.mp (takeWhile_getLast ha))
    have key := le_ofSummands_prepend hnfl
    rwa [e1] at key

theorem eq_zero_of_summands_nil {y : Tm} (h : summands y = []) : y = .zero := by
  cases y <;> simp_all [summands]

theorem oadd_eq_ofSummands {x y h : Tm} {r : List Tm} (hx : WNF x) (hy : WNF y)
    (hs : summands y = h :: r) :
    oadd x y = ofSummands ((summands x).takeWhile (fun s => leB h s) ++ summands y) := by
  have hX := nfl_summands hx
  have hY := nfl_summands hy
  have := ofSummands_summands (oadd x y) (wnf_oadd hx hy)
  rw [summands_oadd hs (fun s hs => (hX.1 s hs).2) (fun s hs => (hY.1 s hs).2)] at this
  exact this.symm

/-- `y ≠ 0` なら `x < x ⊕ y` -/
theorem lt_oadd_left {x y : Tm} (hx : WNF x) (hy : WNF y) (hy0 : y ≠ .zero) : Lt x (oadd x y) := by
  cases hs : summands y with
  | nil => exact absurd (eq_zero_of_summands_nil hs) hy0
  | cons h r =>
    have hX := nfl_summands hx
    have hY := nfl_summands hy
    have hXp : ∀ s, s ∈ summands x → isPrincipal s = true := fun s hs => (hX.1 s hs).2
    have hYp : ∀ s, s ∈ summands y → isPrincipal s = true := fun s hs => (hY.1 s hs).2
    unfold Lt
    rw [cmp_eq, summands_oadd hs hXp hYp]
    have hLD := List.takeWhile_append_dropWhile (p := fun s => leB h s) (l := summands x)
    generalize hD : (summands x).dropWhile (fun s => leB h s) = D at hLD
    generalize hL : (summands x).takeWhile (fun s => leB h s) = L at hLD ⊢
    rw [← hLD, cmpList_append_same, hs]
    subst hL
    cases hd : D with
    | nil => exact cmpList_nil_cons _ _
    | cons d rest =>
      subst hd
      have hdn := head_dropWhile_not hD
      have hdm : d ∈ summands x := by
        have := List.dropWhile_sublist (p := fun s => leB h s) (l := summands x)
        exact this.subset (by rw [hD]; exact List.mem_cons_self)
      have hdp := hXp d hdm
      have hhp : isPrincipal h = true := hYp h (by rw [hs]; exact List.mem_cons_self)
      have hd' : ¬ cmp h d ≠ .gt := by
        intro e; rw [← leB_iff] at e; rw [e] at hdn; cases hdn
      rw [cmp_principal hhp hdp] at hd'
      have e1 : cmpP h d = .gt := by
        cases e : cmpP h d <;> simp_all
      have hdF := (hX.1 d hdm).1
      have hhF := (hY.1 h (by rw [hs]; exact List.mem_cons_self)).1
      have e2 : cmpP d h = .lt := by
        have := swapY hdF hhF
        rw [cmp_principal hdp hhp, cmp_principal hhp hdp, e1] at this
        revert this; cases cmpP d h <;> simp [Ordering.swap]
      exact cmpList_head_lt _ _ e2

theorem head_mem {y h : Tm} {r : List Tm} (hs : summands y = h :: r) : h ∈ summands y := by
  rw [hs]; exact List.mem_cons_self

/-- `oadd x ·` は狭義単調 -/
theorem oadd_lt_oadd {x y y' : Tm} (hx : WNF x) (hy : WNF y) (hy' : WNF y') (hlt : Lt y y') :
    Lt (oadd x y) (oadd x y') := by
  have hy'0 : y' ≠ .zero := by intro e; rw [e] at hlt; exact not_lt_zero y hlt
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs, oadd_zero]; exact lt_oadd_left hx hy' hy'0
  | cons h r =>
    cases hs' : summands y' with
    | nil => exact absurd (eq_zero_of_summands_nil hs') hy'0
    | cons h' r' =>
      have hX := nfl_summands hx
      have hY := nfl_summands hy
      have hY' := nfl_summands hy'
      have hXp : ∀ s, s ∈ summands x → isPrincipal s = true := fun s hs => (hX.1 s hs).2
      have hYp : ∀ s, s ∈ summands y → isPrincipal s = true := fun s hs => (hY.1 s hs).2
      have hYp' : ∀ s, s ∈ summands y' → isPrincipal s = true := fun s hs => (hY'.1 s hs).2
      have hhF := hY.1 h (head_mem hs)
      have hhF' := hY'.1 h' (head_mem hs')
      have hle := head_le_of_lt hs hs' hlt
      unfold Lt
      rw [cmp_eq, summands_oadd hs hXp hYp, summands_oadd hs' hXp hYp']
      cases e : cmpP h h' with
      | gt => exact absurd e hle
      | eq =>
        have := eq_of_cmpP_eqY hhF.1 hhF'.1 hhF.2 hhF'.2 e
        subst this
        rw [cmpList_append_same, ← cmp_eq]
        exact hlt
      | lt =>
        -- L = L' ++ M
        have hLD := List.takeWhile_append_dropWhile (p := fun s => leB h' s) (l := summands x)
        have hall : ∀ a, a ∈ (summands x).takeWhile (fun s => leB h' s) → leB h a = true := by
          intro a ha
          have ha' := leB_iff.mp (mem_takeWhile_imp ha)
          have haF := (hX.1 a ((List.takeWhile_sublist _).subset ha)).1
          rw [leB_iff]
          have h1 : Lt h h' := by
            show cmp h h' = .lt
            rw [cmp_principal hhF.2 hhF'.2]; exact e
          have h2 : Le h' a := le_of_ne_gtY hhF'.1 haF ha'
          exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hhF.1 hhF'.1 haF h1 h2))
        have eL : (summands x).takeWhile (fun s => leB h s) =
            (summands x).takeWhile (fun s => leB h' s) ++
              ((summands x).dropWhile (fun s => leB h' s)).takeWhile (fun s => leB h s) := by
          conv => lhs; rw [← hLD]
          exact takeWhile_append_of_all _ hall
        rw [eL, List.append_assoc, cmpList_append_same]
        cases hM : ((summands x).dropWhile (fun s => leB h' s)).takeWhile (fun s => leB h s) with
        | nil => rw [List.nil_append, ← cmp_eq]; exact hlt
        | cons m rest =>
          rw [List.cons_append, hs']
          -- m は dropWhile の先頭なので h' 未満
          cases hD : (summands x).dropWhile (fun s => leB h' s) with
          | nil => rw [hD] at hM; cases hM
          | cons d drest =>
            rw [hD] at hM
            have hmd : m = d := by
              simp only [List.takeWhile_cons] at hM
              split at hM
              · simp only [List.cons.injEq] at hM; exact hM.1.symm
              · cases hM
            subst hmd
            have hdn := head_dropWhile_not hD
            have hdm : m ∈ summands x := by
              have := List.dropWhile_sublist (p := fun s => leB h' s) (l := summands x)
              exact this.subset (by rw [hD]; exact List.mem_cons_self)
            have hmF := hX.1 m hdm
            have : ¬ cmp h' m ≠ .gt := by
              intro e'; rw [← leB_iff] at e'; rw [e'] at hdn; cases hdn
            rw [cmp_principal hhF'.2 hmF.2] at this
            have e1 : cmpP h' m = .gt := by cases e' : cmpP h' m <;> simp_all
            have e2 : cmpP m h' = .lt := by
              have := swapY hmF.1 hhF'.1
              rw [cmp_principal hmF.2 hhF'.2, cmp_principal hhF'.2 hmF.2, e1] at this
              revert this; cases cmpP m h' <;> simp [Ordering.swap]
            exact cmpList_head_lt _ _ e2

/-- 主要項 `z` より小さいものの和は `z` より小さい -/
theorem oadd_lt_prin {x y z : Tm} (hx : WNF x) (hy : WNF y) (hzp : isPrincipal z = true)
    (h1 : Lt x z) (h2 : Lt y z) : Lt (oadd x y) z := by
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs, oadd_zero]; exact h1
  | cons h r =>
    have hX := nfl_summands hx
    have hY := nfl_summands hy
    have hXp : ∀ s, s ∈ summands x → isPrincipal s = true := fun s hs => (hX.1 s hs).2
    have hYp : ∀ s, s ∈ summands y → isPrincipal s = true := fun s hs => (hY.1 s hs).2
    have hS := summands_oadd hs hXp hYp
    cases hL : (summands x).takeWhile (fun s => leB h s) with
    | nil =>
      rw [hL, List.nil_append, hs] at hS
      exact lt_of_head_lt hzp hS (head_lt_prin hs hzp h2)
    | cons a rest =>
      rw [hL, List.cons_append] at hS
      cases hsx : summands x with
      | nil => rw [hsx] at hL; cases hL
      | cons a' rest' =>
        have haa : a = a' := by
          rw [hsx] at hL
          simp only [List.takeWhile_cons] at hL
          split at hL
          · simp only [List.cons.injEq] at hL; exact hL.1.symm
          · cases hL
        subst haa
        exact lt_of_head_lt hzp hS (head_lt_prin hsx hzp h1)

/-! ### 自然な和 -/

/-- 大きい順の列の要素は先頭以下 -/
theorem le_head_of_nfl : ∀ {x : Tm} {l : List Tm}, NFL (x :: l) → ∀ z, z ∈ l → cmp z x ≠ .gt
  | _, [], _, z, hz => by cases hz
  | x, y :: rest, h, z, hz => by
    have hy := h.2.1
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · have ih := le_head_of_nfl (nfl_tail h) z hz
      have hxF := (h.1 x List.mem_cons_self).1
      have hyF := (h.1 y (List.mem_cons_of_mem _ List.mem_cons_self)).1
      have hzF := (h.1 z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))).1
      exact ne_gt_of_le (le_transY hzF hyF hxF (le_of_ne_gtY hzF hyF ih) (le_of_ne_gtY hyF hxF hy))

theorem mem_merge : ∀ {l m : List Tm} {a : Tm}, a ∈ merge l m → a ∈ l ∨ a ∈ m
  | [], m, a, h => by rw [merge.eq_1] at h; exact Or.inr h
  | x :: xs, [], a, h => by rw [merge.eq_2] at h; exact Or.inl h
  | x :: xs, y :: ys, a, h => by
    rw [merge.eq_3] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_merge h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases mem_merge h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
termination_by l m => l.length + m.length

theorem nfl_merge : ∀ {l m : List Tm}, NFL l → NFL m → NFL (merge l m)
  | [], m, _, hm => by rw [merge.eq_1]; exact hm
  | x :: xs, [], hl, _ => by rw [merge.eq_2]; exact hl
  | x :: xs, y :: ys, hl, hm => by
    have hxF := hl.1 x List.mem_cons_self
    have hyF := hm.1 y List.mem_cons_self
    have hall : ∀ z, z ∈ merge xs (y :: ys) ∨ z ∈ merge (x :: xs) ys →
        z ∈ x :: xs ∨ z ∈ y :: ys := by
      intro z hz
      rcases hz with hz | hz <;> rcases mem_merge hz with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    rw [merge.eq_3]
    split
    · rename_i hyx
      have ih := nfl_merge (nfl_tail hl) hm
      refine ⟨fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hxF
        · rcases hall z (Or.inl hz) with h | h
          · exact hl.1 z h
          · exact hm.1 z h
      · cases hmg : merge xs (y :: ys) with
        | nil => trivial
        | cons w rest =>
          rw [hmg] at ih
          refine ⟨?_, ih.2⟩
          have hw : w ∈ merge xs (y :: ys) := by rw [hmg]; exact List.mem_cons_self
          rcases mem_merge hw with h | h
          · exact le_head_of_nfl hl w h
          · have hwF := (hm.1 w h).1
            rcases List.mem_cons.mp h with rfl | h
            · exact leB_iff.mp hyx
            · exact ne_gt_of_le (le_transY hwF hyF.1 hxF.1
                (le_of_ne_gtY hwF hyF.1 (le_head_of_nfl hm w h))
                (le_of_ne_gtY hyF.1 hxF.1 (leB_iff.mp hyx)))
    · rename_i hyx
      have hxy : cmp x y ≠ .gt := by
        have : cmp y x = .gt := by
          have := leB_iff (a := y) (b := x); simp_all
        have hs := swapY hyF.1 hxF.1
        rw [this] at hs; rw [hs]; decide
      have ih := nfl_merge hl (nfl_tail hm)
      refine ⟨fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hyF
        · rcases hall z (Or.inr hz) with h | h
          · exact hl.1 z h
          · exact hm.1 z h
      · cases hmg : merge (x :: xs) ys with
        | nil => trivial
        | cons w rest =>
          rw [hmg] at ih
          refine ⟨?_, ih.2⟩
          have hw : w ∈ merge (x :: xs) ys := by rw [hmg]; exact List.mem_cons_self
          rcases mem_merge hw with h | h
          · have hwF := (hl.1 w h).1
            rcases List.mem_cons.mp h with rfl | h
            · exact hxy
            · exact ne_gt_of_le (le_transY hwF hxF.1 hyF.1
                (le_of_ne_gtY hwF hxF.1 (le_head_of_nfl hl w h)) (le_of_ne_gtY hxF.1 hyF.1 hxy))
          · exact le_head_of_nfl hm w h
termination_by l m => l.length + m.length

theorem wnf_nsum {x y : Tm} (hx : WNF x) (hy : WNF y) : WNF (nsum x y) :=
  wnf_ofSummands (nfl_merge (nfl_summands hx) (nfl_summands hy))

theorem nsum_zero (x : Tm) (hx : WNF x) : nsum x .zero = x := by
  unfold nsum
  cases hs : summands x with
  | nil => rw [show summands Tm.zero = [] from rfl, merge.eq_1]; rw [← hs]; exact ofSummands_summands x hx
  | cons a l => rw [show summands Tm.zero = [] from rfl, merge.eq_2, ← hs]; exact ofSummands_summands x hx

theorem zero_nsum (y : Tm) (hy : WNF y) : nsum .zero y = y := by
  unfold nsum
  rw [show summands Tm.zero = [] from rfl, merge.eq_1]
  exact ofSummands_summands y hy

theorem cmpP_swapP {a b : Tm} (ha : WNF a ∧ isPrincipal a = true) (hb : WNF b ∧ isPrincipal b = true) :
    cmpP b a = (cmpP a b).swap := by
  have := swapY ha.1 hb.1
  rwa [cmp_principal ha.2 hb.2, cmp_principal hb.2 ha.2] at this

theorem leB_principal {a b : Tm} (ha : isPrincipal a = true) (hb : isPrincipal b = true) :
    leB a b = true ↔ cmpP a b ≠ .gt := by
  rw [leB_iff, cmp_principal ha hb]

/-- 空でない列を併合すると大きくなる -/
theorem lt_merge_nonempty : ∀ {A B : List Tm}, NFL A → NFL B → B ≠ [] → cmpList A (merge A B) = .lt
  | [], _, _, _, hB => by
    rw [merge.eq_1]; cases ‹List Tm› with
    | nil => exact absurd rfl hB
    | cons _ _ => exact cmpList_nil_cons _ _
  | _, [], _, _, hB => absurd rfl hB
  | a :: As, b :: Bs, hA, hB, _ => by
    have haF := hA.1 a List.mem_cons_self
    have hbF := hB.1 b List.mem_cons_self
    rw [merge.eq_3]
    split
    · rw [cmpList_cons_cons_eq _ _ (cmpP_self a)]
      exact lt_merge_nonempty (nfl_tail hA) hB (by simp)
    · rename_i hba
      rw [leB_principal hbF.2 haF.2] at hba
      have e1 : cmpP b a = .gt := by cases e : cmpP b a <;> simp_all
      have e2 : cmpP a b = .lt := by
        rw [cmpP_swapP hbF haF, e1]; rfl
      exact cmpList_head_lt _ _ e2
termination_by A B => A.length + B.length

/-- 併合は右の列について狭義単調 -/
theorem cmpList_merge_right : ∀ {A B B' : List Tm}, NFL A → NFL B → NFL B' → cmpList B B' = .lt →
    cmpList (merge A B) (merge A B') = .lt
  | [], B, B', _, _, _, h => by rw [merge.eq_1, merge.eq_1]; exact h
  | a :: As, [], B', hA, _, hB', h => by
    rw [merge.eq_2]
    cases B' with
    | nil => rw [cmpList_nil_nil] at h; cases h
    | cons _ _ => exact lt_merge_nonempty hA hB' (by simp)
  | a :: As, b :: Bs, [], _, _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | a :: As, b :: Bs, b' :: Bs', hA, hB, hB', h => by
    have haF := hA.1 a List.mem_cons_self
    have hbF := hB.1 b List.mem_cons_self
    have hbF' := hB'.1 b' List.mem_cons_self
    have hbb : cmpP b b' ≠ .gt := by
      rcases cmpList_lt_cases h with e | ⟨e, -⟩ <;> rw [e] <;> decide
    rw [merge.eq_3, merge.eq_3]
    by_cases h1 : leB b a = true
    · rw [ite_eq_left h1]
      by_cases h2 : leB b' a = true
      · rw [ite_eq_left h2, cmpList_cons_cons_eq _ _ (cmpP_self a)]
        exact cmpList_merge_right (nfl_tail hA) hB hB' h
      · rw [ite_eq_right h2]
        rw [leB_principal hbF'.2 haF.2] at h2
        have e1 : cmpP b' a = .gt := by cases e : cmpP b' a <;> simp_all
        have e2 : cmpP a b' = .lt := by rw [cmpP_swapP hbF' haF, e1]; rfl
        exact cmpList_head_lt _ _ e2
    · rw [ite_eq_right h1]
      rw [leB_principal hbF.2 haF.2] at h1
      have e1 : cmpP b a = .gt := by cases e : cmpP b a <;> simp_all
      by_cases h2 : leB b' a = true
      · -- b > a ≥ b' は b ≤ b' に反する
        exfalso
        rw [leB_principal hbF'.2 haF.2] at h2
        have l1 : Lt a b := by
          show cmp a b = .lt
          rw [cmp_principal haF.2 hbF.2, cmpP_swapP hbF haF, e1]; rfl
        have l2 : Le b' a := le_of_ne_gtY hbF'.1 haF.1 (by rw [cmp_principal hbF'.2 haF.2]; exact h2)
        have l3 : Le b b' := le_of_ne_gtY hbF.1 hbF'.1 (by rw [cmp_principal hbF.2 hbF'.2]; exact hbb)
        have := lt_of_lt_of_leY haF.1 hbF.1 haF.1 l1 (le_transY hbF.1 hbF'.1 haF.1 l3 l2)
        exact Lt.irrefl a this
      · rw [ite_eq_right h2]
        cases e : cmpP b b' with
        | gt => exact absurd e hbb
        | lt => exact cmpList_head_lt _ _ e
        | eq =>
          have := eq_of_cmpP_eqY hbF.1 hbF'.1 hbF.2 hbF'.2 e
          subst this
          rw [cmpList_cons_cons_eq _ _ e]
          rw [cmpList_cons_cons_eq _ _ e] at h
          exact cmpList_merge_right hA (nfl_tail hB) (nfl_tail hB') h
termination_by A B B' => A.length + B.length + B'.length

theorem nfl_principal {l : List Tm} (h : NFL l) : ∀ x, x ∈ l → isPrincipal x = true :=
  fun x hx => (h.1 x hx).2

/-- 列の比較の推移性（`≤` どうし） -/
theorem cmpList_le_trans {l1 l2 l3 : List Tm} (h1 : NFL l1) (h2 : NFL l2) (h3 : NFL l3)
    (a : cmpList l1 l2 ≠ .gt) (b : cmpList l2 l3 ≠ .gt) : cmpList l1 l3 ≠ .gt := by
  rw [← cmp_ofSummands (nfl_principal h1) (nfl_principal h2)] at a
  rw [← cmp_ofSummands (nfl_principal h2) (nfl_principal h3)] at b
  rw [← cmp_ofSummands (nfl_principal h1) (nfl_principal h3)]
  have w1 := wnf_ofSummands h1
  have w2 := wnf_ofSummands h2
  have w3 := wnf_ofSummands h3
  exact ne_gt_of_le (le_transY w1 w2 w3 (le_of_ne_gtY w1 w2 a) (le_of_ne_gtY w2 w3 b))

theorem length_merge : ∀ (A B : List Tm), (merge A B).length = A.length + B.length
  | [], B => by rw [merge.eq_1]; simp
  | a :: As, [] => by rw [merge.eq_2]; simp
  | a :: As, b :: Bs => by
    rw [merge.eq_3]
    split
    · simp only [List.length_cons, length_merge As (b :: Bs)]; omega
    · simp only [List.length_cons, length_merge (a :: As) Bs]; omega
termination_by A B => A.length + B.length

/-- 長さの違う列は比較で等しくならない -/
theorem cmpList_ne_eq_of_length {l1 l2 : List Tm} (h1 : NFL l1) (h2 : NFL l2) (hl : l1.length ≠ l2.length) :
    cmpList l1 l2 ≠ .eq := by
  intro e
  have := eq_of_cmpList_eq l1 l2 (fun x hx y hy hxy =>
    eq_of_cmpP_eqY (h1.1 x hx).1 (h2.1 y hy).1 (h1.1 x hx).2 (h2.1 y hy).2 hxy) e
  rw [this] at hl; exact hl rfl

theorem lt_of_le_of_ne_eq {o : Ordering} (h1 : o ≠ .gt) (h2 : o ≠ .eq) : o = .lt := by
  cases o <;> simp_all

/-- 左から併合しても小さくならない -/
theorem le_merge_left : ∀ {A B : List Tm}, NFL A → NFL B → cmpList B (merge A B) ≠ .gt
  | [], B, _, _ => by rw [merge.eq_1, cmpList_self B (fun x _ => cmpP_self x)]; decide
  | a :: As, [], _, _ => by rw [merge.eq_2]; rw [cmpList_nil_cons]; decide
  | a :: As, b :: Bs, hA, hB => by
    have haF := hA.1 a List.mem_cons_self
    have hbF := hB.1 b List.mem_cons_self
    rw [merge.eq_3]
    split
    · rename_i hba
      rw [leB_principal hbF.2 haF.2] at hba
      cases e : cmpP b a with
      | gt => exact absurd e hba
      | lt => rw [cmpList_head_lt _ _ e]; decide
      | eq =>
        have := eq_of_cmpP_eqY hbF.1 haF.1 hbF.2 haF.2 e
        subst this
        rw [cmpList_cons_cons_eq _ _ e]
        -- Bs ≤ b :: Bs ≤ merge As (b :: Bs)
        have hm := nfl_merge (nfl_tail hA) hB
        exact cmpList_le_trans (nfl_tail hB) hB hm (by
          have := cmpList_cons_ge (nfl_tail hB) hbF.1 hbF.2 (fun c hc => by
            cases Bs with
            | nil => cases hc
            | cons c' rest => simp only [List.head?_cons, Option.some.injEq] at hc; rw [← hc]; exact hB.2.1)
          exact this) (le_merge_left (nfl_tail hA) hB)
    · rw [cmpList_cons_cons_eq _ _ (cmpP_self b)]
      exact le_merge_left hA (nfl_tail hB)
termination_by A B => A.length + B.length

theorem lt_merge_left {A B : List Tm} (hA : NFL A) (hB : NFL B) (hne : A ≠ []) :
    cmpList B (merge A B) = .lt := by
  refine lt_of_le_of_ne_eq (le_merge_left hA hB) (cmpList_ne_eq_of_length hB (nfl_merge hA hB) ?_)
  rw [length_merge]
  cases A with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

/-! #### 自然な和の大小 -/

theorem nsum_lt_right {x y y' : Tm} (hx : WNF x) (hy : WNF y) (hy' : WNF y') (h : Lt y y') :
    Lt (nsum x y) (nsum x y') := by
  unfold Lt nsum
  have hX := nfl_summands hx
  have hY := nfl_summands hy
  have hY' := nfl_summands hy'
  rw [cmp_ofSummands (nfl_principal (nfl_merge hX hY)) (nfl_principal (nfl_merge hX hY'))]
  apply cmpList_merge_right hX hY hY'
  have := h; unfold Lt at this; rwa [cmp_eq] at this

theorem lt_nsum_left {x y : Tm} (hx : WNF x) (hy : WNF y) (hy0 : y ≠ .zero) : Lt x (nsum x y) := by
  unfold Lt nsum
  have hX := nfl_summands hx
  have hY := nfl_summands hy
  have key := cmp_ofSummands (nfl_principal hX) (nfl_principal (nfl_merge hX hY))
  rw [ofSummands_summands x hx] at key
  rw [key]
  exact lt_merge_nonempty hX hY (summands_ne_nil hy0)

theorem lt_nsum_right {x y : Tm} (hx : WNF x) (hy : WNF y) (hx0 : x ≠ .zero) : Lt y (nsum x y) := by
  unfold Lt nsum
  have hX := nfl_summands hx
  have hY := nfl_summands hy
  have key := cmp_ofSummands (nfl_principal hY) (nfl_principal (nfl_merge hX hY))
  rw [ofSummands_summands y hy] at key
  rw [key]
  exact lt_merge_left hX hY (summands_ne_nil hx0)

theorem le_nsum_right {x y : Tm} (hx : WNF x) (hy : WNF y) : Le y (nsum x y) := by
  by_cases hx0 : x = .zero
  · subst hx0; rw [zero_nsum y hy]; exact Le.refl y
  · exact Or.inr (lt_nsum_right hx hy hx0)

theorem le_nsum_left {x y : Tm} (hx : WNF x) (hy : WNF y) : Le x (nsum x y) := by
  by_cases hy0 : y = .zero
  · subst hy0; rw [nsum_zero x hx]; exact Le.refl x
  · exact Or.inr (lt_nsum_left hx hy hy0)

/-- 併合の先頭はどちらかの先頭 -/
theorem merge_head : ∀ {A B : List Tm} {h : Tm} {rest : List Tm}, merge A B = h :: rest →
    A.head? = some h ∨ B.head? = some h
  | [], B, h, rest, e => by rw [merge.eq_1] at e; rw [e]; exact Or.inr rfl
  | a :: As, [], h, rest, e => by rw [merge.eq_2] at e; simp only [List.cons.injEq] at e; rw [e.1]; exact Or.inl rfl
  | a :: As, b :: Bs, h, rest, e => by
    rw [merge.eq_3] at e
    split at e <;> (simp only [List.cons.injEq] at e; rw [← e.1])
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem nsum_lt_prin {x y z : Tm} (hx : WNF x) (hy : WNF y) (hzp : isPrincipal z = true)
    (h1 : Lt x z) (h2 : Lt y z) : Lt (nsum x y) z := by
  unfold nsum
  have hX := nfl_summands hx
  have hY := nfl_summands hy
  cases hm : merge (summands x) (summands y) with
  | nil =>
    show cmp (ofSummands []) z = .lt
    rw [show ofSummands [] = Tm.zero from rfl]
    have : z ≠ .zero := by intro e; rw [e] at hzp; cases hzp
    exact zero_lt this
  | cons h rest =>
    have hS : summands (ofSummands (h :: rest)) = h :: rest :=
      summands_ofSummands _ (by rw [← hm]; exact nfl_principal (nfl_merge hX hY))
    refine lt_of_head_lt hzp hS ?_
    rcases merge_head hm with e | e
    · cases hs : summands x with
      | nil => rw [hs] at e; cases e
      | cons a l => rw [hs] at e; simp only [List.head?_cons, Option.some.injEq] at e; subst e
                    exact head_lt_prin hs hzp h1
    · cases hs : summands y with
      | nil => rw [hs] at e; cases e
      | cons a l => rw [hs] at e; simp only [List.head?_cons, Option.some.injEq] at e; subst e
                    exact head_lt_prin hs hzp h2

/-! ### 倍 `B·n` -/

theorem nfl_replicate {x : Tm} (hx : WNF x) (hxp : isPrincipal x = true) : ∀ n, NFL (List.replicate n x)
  | 0 => ⟨by simp, trivial⟩
  | 1 => nfl_of_wnf_principal hx hxp
  | n + 2 => by
    have ih := nfl_replicate hx hxp (n + 1)
    refine ⟨fun y hy => by rw [List.eq_of_mem_replicate hy]; exact ⟨hx, hxp⟩, ?_⟩
    show cmp x x ≠ .gt ∧ Desc (List.replicate (n + 1) x)
    exact ⟨by rw [cmp_self]; decide, ih.2⟩

theorem wnf_mulNat {x : Tm} (hx : WNF x) (hxp : isPrincipal x = true) (n : Nat) : WNF (mulNat x n) :=
  wnf_ofSummands (nfl_replicate hx hxp n)

theorem mulNat_lt_succ {x : Tm} (hxp : isPrincipal x = true) (n : Nat) :
    Lt (mulNat x n) (mulNat x (n + 1)) := by
  unfold Lt mulNat
  have hp : ∀ m, ∀ y, y ∈ List.replicate m x → isPrincipal y = true :=
    fun m y hy => by rw [List.eq_of_mem_replicate hy]; exact hxp
  rw [cmp_ofSummands (hp n) (hp (n + 1)), List.replicate_succ']
  exact cmpList_append_lt _ _ (by simp)

theorem mulNat_lt_mulNat {x : Tm} (hx : WNF x) (hxp : isPrincipal x = true) {n m : Nat} (h : n < m) :
    Lt (mulNat x n) (mulNat x m) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact lt_transY (wnf_mulNat hx hxp n) (wnf_mulNat hx hxp m) (wnf_mulNat hx hxp (m + 1))
        (ih h) (mulNat_lt_succ hxp m)
    · exact mulNat_lt_succ hxp n

theorem summands_mulNat {x : Tm} (hxp : isPrincipal x = true) (n : Nat) :
    summands (mulNat x n) = List.replicate n x :=
  summands_ofSummands _ (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact hxp)

theorem mulNat_lt_prin {x z : Tm} (hxp : isPrincipal x = true) (hzp : isPrincipal z = true)
    (h : Lt x z) (n : Nat) : Lt (mulNat x n) z := by
  cases n with
  | zero =>
    show cmp Tm.zero z = .lt
    have : z ≠ .zero := by intro e; rw [e] at hzp; cases hzp
    exact zero_lt this
  | succ n =>
    have hs : summands (mulNat x (n + 1)) = x :: List.replicate n x := by
      rw [summands_mulNat hxp]; rfl
    refine lt_of_head_lt hzp hs ?_
    have := h; unfold Lt at this; rwa [cmp_principal hxp hzp] at this

end MahloOCF.FS
