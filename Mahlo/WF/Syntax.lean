import Mahlo.Notation

/-! 構成的な整列性証明（`Mahlo/WF`）の土台：`cmp`・`inC`・前線 `fr` の構文的な性質。

順序数・`Classical.choice`・大基数の仮定を使わず、項の大きさについての帰納法だけで示す
（Compact リポジトリの `Compact/WF/Syntax.lean` と同じ構成）。

* `cmp` の展開（和は先頭の主要項から辞書式、主要項は階・形ごと）と `cmp_self`。
* `Lt`・`Le`、部分項の一覧 `subs`。
* `inC`（`α ∈ C(γ, δ)`）の展開と単調性。
* 前線 `fr R x`（`x` の `R` 未満の極大の崩壊の節点）と、`inC` の前線による言い換え。 -/

namespace MahloOCF

open Tm

theorem cmpList_nil_nil : cmpList [] [] = .eq := by rw [cmpList]

theorem cmpList_nil_cons (y : Tm) (ys : List Tm) : cmpList [] (y :: ys) = .lt := by rw [cmpList]

theorem cmpList_cons_nil (x : Tm) (xs : List Tm) : cmpList (x :: xs) [] = .gt := by rw [cmpList]

theorem cmpList_cons_cons_eq {x y : Tm} (xs ys : List Tm) (h : cmpP x y = .eq) :
    cmpList (x :: xs) (y :: ys) = cmpList xs ys := by
  rw [cmpList, h]

theorem cmpList_cons_cons_ne {x y : Tm} (xs ys : List Tm) (h : cmpP x y ≠ .eq) :
    cmpList (x :: xs) (y :: ys) = cmpP x y := by
  rw [cmpList]
  cases e : cmpP x y with
  | eq => exact absurd e h
  | lt => rfl
  | gt => rfl

theorem cmp_eq (a b : Tm) : cmp a b = cmpList (summands a) (summands b) := by rw [cmp]

theorem cmpList_self : ∀ l : List Tm, (∀ x, x ∈ l → cmpP x x = .eq) → cmpList l l = .eq
  | [], _ => cmpList_nil_nil
  | x :: xs, h => by
    rw [cmpList_cons_cons_eq xs xs (h x List.mem_cons_self)]
    exact cmpList_self xs (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem size_le_of_mem_summands : ∀ (t s : Tm), s ∈ summands t → s.size ≤ t.size
  | .zero, s, h => by simp [summands] at h
  | .plus a b, s, h => by
    rw [summands, List.mem_cons] at h
    cases h with
    | inl e => rw [e]; simp only [Tm.size]; omega
    | inr h => have := size_le_of_mem_summands b s h; simp only [Tm.size]; omega
  | .M _, s, h | .Om _, s, h | .Xi _ _, s, h | .Psi _ _, s, h => by
    simp only [summands, List.mem_singleton] at h
    rw [h]
    exact Nat.le_refl _

theorem cmpPsi_self (pi a : Tm) (h : cmp a a = .eq) : cmpPsi (.Psi pi a) (.Psi pi a) = .eq := by
  rw [cmpPsi.eq_def]
  simp only [beq_self_eq_true, ↓reduceIte]
  exact h

theorem cmp_self_aux : ∀ n, ∀ t : Tm, t.size ≤ n → cmp t t = .eq ∧ cmpP t t = .eq := by
  intro n
  induction n with
  | zero => intro t h; exact absurd h (Nat.not_le.mpr (Tm.size_pos t))
  | succ n ih =>
    intro t ht
    have hP : ∀ x : Tm, x.size ≤ n + 1 → cmpP x x = .eq := by
      intro x hx
      rw [cmpP.eq_def]
      simp only [Nat.lt_irrefl, ↓reduceIte]
      cases x with
      | Om a =>
        have := (ih a (by simp only [Tm.size] at hx; omega)).1
        simpa using this
      | Xi m a => simp
      | Psi pi a =>
        exact cmpPsi_self pi a (ih a (by simp only [Tm.size] at hx; omega)).1
      | _ => rfl
    refine ⟨?_, hP t ht⟩
    rw [cmp_eq]
    exact cmpList_self _ (fun x hx => hP x (Nat.le_trans (size_le_of_mem_summands t x hx) ht))

/-- `cmp t t = .eq` -/
theorem cmp_self (t : Tm) : cmp t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).1

theorem cmpP_self (t : Tm) : cmpP t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).2

theorem isNF_plus {a b : Tm} (h : isNF (.plus a b) = true) : isNF a = true ∧ isNF b = true := by
  simp only [isNF, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem ofSummands_summands : ∀ t : Tm, isNF t = true → ofSummands (summands t) = t
  | .zero, _ => rfl
  | .M _, _ | .Om _, _ | .Xi _ _, _ | .Psi _ _, _ => rfl
  | .plus a b, h => by
    have hb0 : b ≠ .zero := by
      simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact h.1.1.1.2
    have ih := ofSummands_summands b (isNF_plus h).2
    rw [summands]
    cases hs : summands b with
    | nil =>
      exfalso
      cases b <;> simp_all [summands]
    | cons s ss =>
      rw [hs] at ih
      show plus a (ofSummands (s :: ss)) = plus a b
      rw [ih]

theorem eq_of_summands_eq {a b : Tm} (ha : isNF a = true) (hb : isNF b = true)
    (h : summands a = summands b) : a = b := by
  rw [← ofSummands_summands a ha, ← ofSummands_summands b hb, h]

theorem cmpList_swap : ∀ l1 l2 : List Tm,
    (∀ x, x ∈ l1 → ∀ y, y ∈ l2 → cmpP y x = (cmpP x y).swap) →
    cmpList l2 l1 = (cmpList l1 l2).swap
  | [], [], _ => by rw [cmpList_nil_nil]; rfl
  | [], _ :: _, _ => by rw [cmpList_cons_nil, cmpList_nil_cons]; rfl
  | _ :: _, [], _ => by rw [cmpList_cons_nil, cmpList_nil_cons]; rfl
  | x :: xs, y :: ys, h => by
    have hxy := h x List.mem_cons_self y List.mem_cons_self
    have ht : ∀ a, a ∈ xs → ∀ b, b ∈ ys → cmpP b a = (cmpP a b).swap :=
      fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    cases e : cmpP x y with
    | eq =>
      have e' : cmpP y x = .eq := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_eq _ _ e, cmpList_cons_cons_eq _ _ e']
      exact cmpList_swap xs ys ht
    | lt =>
      have e' : cmpP y x = .gt := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_ne _ _ (by rw [e']; decide), cmpList_cons_cons_ne _ _ (by rw [e]; decide),
        e, e']
      rfl
    | gt =>
      have e' : cmpP y x = .lt := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_ne _ _ (by rw [e']; decide), cmpList_cons_cons_ne _ _ (by rw [e]; decide),
        e, e']
      rfl

theorem eq_of_cmpList_eq : ∀ l1 l2 : List Tm,
    (∀ x, x ∈ l1 → ∀ y, y ∈ l2 → cmpP x y = .eq → x = y) →
    cmpList l1 l2 = .eq → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by rw [cmpList_nil_cons] at h; cases h
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hxy, h => by
    cases e : cmpP x y with
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e] at h
      rw [hxy x List.mem_cons_self y List.mem_cons_self e,
        eq_of_cmpList_eq xs ys (fun a ha b hb => hxy a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb)) h]
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h

theorem cmp_principal {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    cmp x y = cmpP x y := by
  rw [cmp_eq, summands_principal hx, summands_principal hy]
  cases e : cmpP x y with
  | eq => rw [cmpList_cons_cons_eq _ _ e, cmpList_nil_nil]
  | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem cmpP_of_lev_lt {x y : Tm} (h : lev x < lev y) : cmpP x y = .lt := by
  rw [cmpP.eq_def, ite_eq_left h]

theorem cmpP_of_lev_gt {x y : Tm} (h : lev y < lev x) : cmpP x y = .gt := by
  rw [cmpP.eq_def, ite_eq_right (Nat.lt_asymm h), ite_eq_left h]

/-! ### 同じ階の主要項どうしの `cmpP` の展開 -/

theorem cmpOmX_psiOm (a c β : Tm) :
    cmpOmX a (.Psi (.Om c) β) = if cmp a c = .lt then .lt else .gt := by
  rw [cmpOmX.eq_def]
  simp only [omegaFixed, isXi, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]

theorem cmpOmX_xi (a b : Tm) (n : Nat) : cmpOmX a (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpOmX.eq_def]
  simp [omegaFixed]

theorem cmpOmX_psiXi (a b β : Tm) (n : Nat) :
    cmpOmX a (.Psi (.Xi n b) β) = cmp a (.Psi (.Xi n b) β) := by
  rw [cmpOmX.eq_def]
  simp [omegaFixed, isXi]

theorem cmpP_M_M {m n : Nat} (h : m = n) : cmpP (.M m) (.M n) = .eq := by
  subst h
  exact cmpP_self _

theorem cmpP_om_om {a b : Tm} (h : max 1 (lev a) = max 1 (lev b)) :
    cmpP (.Om a) (.Om b) = cmp a b := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpP_om_psiOm {a c β : Tm} (h : max 1 (lev a) = max 1 (lev c)) :
    cmpP (.Om a) (.Psi (.Om c) β) = if cmp a c = .lt then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_psiOm a c β

theorem cmpP_psiOm_om {a c β : Tm} (h : max 1 (lev a) = max 1 (lev c)) :
    cmpP (.Psi (.Om c) β) (.Om a) = (if cmp a c = .lt then Ordering.lt else .gt).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_psiOm]

theorem cmpP_om_xi {a b : Tm} {n : Nat} (h : max 1 (lev a) = n) :
    cmpP (.Om a) (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_xi a b n

theorem cmpP_xi_om {a b : Tm} {n : Nat} (h : max 1 (lev a) = n) :
    cmpP (.Xi n b) (.Om a) = (cmp a (.Xi n b)).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_xi]

theorem cmpP_om_psiXi {a b β : Tm} {n : Nat} (h : max 1 (lev a) = n) :
    cmpP (.Om a) (.Psi (.Xi n b) β) = cmp a (.Psi (.Xi n b) β) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_psiXi a b β n

theorem cmpP_psiXi_om {a b β : Tm} {n : Nat} (h : max 1 (lev a) = n) :
    cmpP (.Psi (.Xi n b) β) (.Om a) = (cmp a (.Psi (.Xi n b) β)).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_psiXi]

theorem cmpP_xi_xi (n : Nat) (a b : Tm) :
    cmpP (.Xi n a) (.Xi n b) =
      if a = b then .eq else if xiLtXi (.Xi n a) (.Xi n b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, Nat.lt_irrefl, ↓reduceIte, beq_iff_eq]

theorem xiLtXi_eq (n m : Nat) (a b : Tm) :
    xiLtXi (.Xi n a) (.Xi m b) =
      ((cmp a b == .lt && inC a b (.Xi m b)) || (cmp b a == .lt && !inC b a (.Xi n a))) := by
  rw [xiLtXi]

theorem cmpP_psi_xi {pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Psi pi a) (.Xi m b) =
      if psiLtXi (.Psi pi a) (.Xi m b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpP_xi_psi {pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Xi m b) (.Psi pi a) =
      if psiLtXi (.Psi pi a) (.Xi m b) = true then .gt else .lt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem psiLtXi_eq (pi a b : Tm) (m : Nat) :
    psiLtXi (.Psi pi a) (.Xi m b) =
      (cmp pi (.Xi m b) != .gt || !(baseOf (.Xi m b) (.Psi pi a))) := by
  rw [psiLtXi]

theorem cmpP_psi_psi {pi a sg b : Tm} (h : lev pi = lev sg) :
    cmpP (.Psi pi a) (.Psi sg b) = cmpPsi (.Psi pi a) (.Psi sg b) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpPsi_eq (pi a sg b : Tm) :
    cmpPsi (.Psi pi a) (.Psi sg b) =
      if pi = sg then cmp a b
      else if cmp sg pi = .lt then (if baseOf sg (.Psi pi a) = true then .gt else .lt)
      else (if baseOf pi (.Psi sg b) = true then .lt else .gt) := by
  rw [cmpPsi.eq_def]
  simp only [beq_iff_eq]

theorem baseOf_om (c t : Tm) :
    baseOf (.Om c) t =
      if isSucc c = true then cmp (omOf (predT c)) t == .lt else (c == zero && t != zero) := by
  rw [baseOf.eq_def]
  simp only []
  split <;> rfl

theorem baseOf_xi (m : Nat) (d t : Tm) :
    baseOf (.Xi m d) t = (cmp (kTerm (m - 1)) t == .lt && inC d d t) := by
  rw [baseOf.eq_def]

/-! ### `<` と `≤` -/

/-- `a < b` -/
def Lt (a b : Tm) : Prop := cmp a b = .lt

instance (a b : Tm) : Decidable (Lt a b) := inferInstanceAs (Decidable (cmp a b = .lt))

theorem Lt.ne {a b : Tm} (h : Lt a b) : a ≠ b := by
  intro e
  subst e
  unfold Lt at h
  rw [cmp_self] at h
  cases h

theorem Lt.irrefl (a : Tm) : ¬ Lt a a := fun h => h.ne rfl

/-- `a ≤ b` -/
def Le (a b : Tm) : Prop := a = b ∨ Lt a b

theorem Le.refl (a : Tm) : Le a a := Or.inl rfl

theorem lev_le_of_cmpP_lt {x y : Tm} (h : cmpP x y = .lt) : lev x ≤ lev y := by
  apply Nat.le_of_not_lt
  intro h'
  rw [cmpP_of_lev_gt h'] at h
  cases h

theorem lt_principal_iff {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    Lt x y ↔ cmpP x y = .lt := by
  unfold Lt
  rw [cmp_principal hx hy]

theorem ite_lt_gt_eq_lt {P : Prop} [Decidable P] :
    ((if P then Ordering.lt else Ordering.gt) = .lt) ↔ P := by
  by_cases h : P
  · simp [h]
  · simp [h]

theorem ite_gt_lt_eq_lt {P : Prop} [Decidable P] :
    ((if P then Ordering.gt else Ordering.lt) = .lt) ↔ ¬ P := by
  by_cases h : P
  · simp [h]
  · simp [h]

/-! ### `inC` の展開 -/

theorem inC_zero (g d : Tm) : inC .zero g d = true := by rw [inC.eq_def]

theorem inC_M (n : Nat) (g d : Tm) : inC (.M n) g d = true := by rw [inC.eq_def]

theorem inC_plus (a b g d : Tm) : inC (.plus a b) g d = (inC a g d && inC b g d) := by
  rw [inC.eq_def]

theorem inC_om (e g d : Tm) : inC (.Om e) g d = inC e g d := by rw [inC.eq_def]

theorem inC_xi (n : Nat) (a g d : Tm) :
    inC (.Xi n a) g d = (cmp (.Xi n a) d == .lt || (inC a g d && cmp a g == .lt)) := by
  rw [inC.eq_def]

theorem inC_psi (k δ g d : Tm) :
    inC (.Psi k δ) g d = (cmp (.Psi k δ) d == .lt ||
      (inC k g d && inC δ g d && cmp δ g == .lt)) := by
  rw [inC.eq_def]

theorem inC_xi_iff {n : Nat} {a g d : Tm} :
    inC (.Xi n a) g d = true ↔ Lt (.Xi n a) d ∨ (inC a g d = true ∧ Lt a g) := by
  rw [inC_xi]
  unfold Lt
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]

/-- `Ψ` の項の `C` への所属：`d` より小さいか、引数が `g` より小さく崩壊先が `C` に入る -/
theorem inC_psi_iff {k δ g d : Tm} :
    inC (.Psi k δ) g d = true ↔
      Lt (.Psi k δ) d ∨ (inC k g d = true ∧ inC δ g d = true ∧ Lt δ g) := by
  rw [inC_psi]
  unfold Lt
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, and_assoc]

/-! ### 部分項 -/

/-- 部分項の一覧（自分自身を含む） -/
def subs : Tm → List Tm
  | .zero => [.zero]
  | .M n => [.M n]
  | .plus a b => .plus a b :: (subs a ++ subs b)
  | .Om a => .Om a :: subs a
  | .Xi n a => .Xi n a :: subs a
  | .Psi k a => .Psi k a :: (subs k ++ subs a)

theorem self_mem_subs (t : Tm) : t ∈ subs t := by
  cases t <;> simp [subs]

theorem size_le_of_mem_subs : ∀ {t s : Tm}, s ∈ subs t → s.size ≤ t.size
  | .zero, s, h | .M _, s, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact Nat.le_refl _
  | .plus a b, s, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
  | .Om a, s, h | .Xi _ a, s, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
  | .Psi p a, s, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega

/-- 大きさが同じ部分項は自分自身 -/
theorem eq_of_mem_subs_size : ∀ {t s : Tm}, s ∈ subs t → t.size ≤ s.size → s = t
  | .zero, s, h, _ | .M _, s, h, _ => by
    simp only [subs, List.mem_singleton] at h
    exact h
  | .plus a b, s, h, hs => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
  | .Om a, s, h, hs | .Xi _ a, s, h, hs => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
  | .Psi p a, s, h, hs => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega

theorem subs_trans : ∀ {t s r : Tm}, s ∈ subs t → r ∈ subs s → r ∈ subs t
  | .zero, s, r, h, hr | .M _, s, r, h, hr => by
    simp only [subs, List.mem_singleton] at h
    subst h
    exact hr
  | .plus a b, s, r, h, hr => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · subst h
      simp only [subs, List.mem_cons, List.mem_append] at hr
      exact hr
    · exact Or.inr (Or.inl (subs_trans h hr))
    · exact Or.inr (Or.inr (subs_trans h hr))
  | .Om a, s, r, h, hr | .Xi _ a, s, r, h, hr => by
    simp only [subs, List.mem_cons] at h ⊢
    rcases h with h | h
    · subst h
      simp only [subs, List.mem_cons] at hr
      exact hr
    · exact Or.inr (subs_trans h hr)
  | .Psi p a, s, r, h, hr => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · subst h
      simp only [subs, List.mem_cons, List.mem_append] at hr
      exact hr
    · exact Or.inr (Or.inl (subs_trans h hr))
    · exact Or.inr (Or.inr (subs_trans h hr))

theorem mem_subs_om (a : Tm) : a ∈ subs (.Om a) := by
  simp [subs, self_mem_subs]

theorem mem_subs_xi (n : Nat) (a : Tm) : a ∈ subs (.Xi n a) := by
  simp [subs, self_mem_subs]

theorem mem_subs_psi_p (k α : Tm) : k ∈ subs (.Psi k α) := by
  simp [subs, self_mem_subs]

theorem mem_subs_psi_a (k α : Tm) : α ∈ subs (.Psi k α) := by
  simp [subs, self_mem_subs]

theorem ne_of_mem_subs_lt {t s : Tm} (h : s.size < t.size) : s ≠ t := by
  intro e
  subst e
  exact Nat.lt_irrefl _ h

theorem subs_plus_l {a b w : Tm} (h : w ∈ subs a) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_plus_r {a b w : Tm} (h : w ∈ subs b) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_om {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Om a) :=
  subs_trans (mem_subs_om a) h

theorem subs_xi {n : Nat} {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Xi n a) :=
  subs_trans (mem_subs_xi n a) h

theorem subs_psi_p {p a w : Tm} (h : w ∈ subs p) : w ∈ subs (.Psi p a) :=
  subs_trans (mem_subs_psi_p p a) h

theorem subs_psi_a {p a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Psi p a) :=
  subs_trans (mem_subs_psi_a p a) h

theorem mem_subs_of_mem_summands : ∀ {t s : Tm}, s ∈ summands t → s ∈ subs t
  | .zero, s, h => by simp [summands] at h
  | .plus a b, s, h => by
    rw [summands, List.mem_cons] at h
    simp only [subs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inr (Or.inl (by rw [h]; exact self_mem_subs a))
    · exact Or.inr (Or.inr (mem_subs_of_mem_summands h))
  | .M _, s, h | .Om _, s, h | .Xi _ _, s, h | .Psi _ _, s, h => by
    simp only [summands, List.mem_singleton] at h
    rw [h]
    exact self_mem_subs _


/-- `S` の上で `<` が推移的 -/
def LinOn (S : List Tm) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → ∀ c, c ∈ S → Lt a b → Lt b c → Lt a c

theorem cmpList_lt_cases {x y : Tm} {xs ys : List Tm} (h : cmpList (x :: xs) (y :: ys) = .lt) :
    cmpP x y = .lt ∨ (cmpP x y = .eq ∧ cmpList xs ys = .lt) := by
  cases e : cmpP x y with
  | lt => exact Or.inl rfl
  | eq => rw [cmpList_cons_cons_eq _ _ e] at h; exact Or.inr ⟨rfl, h⟩
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h

theorem summands_ne_nil {c : Tm} (hc : c ≠ .zero) : summands c ≠ [] := by
  intro h
  cases c <;> simp_all [summands]

theorem lev_head {c h : Tm} {rest : List Tm} (hc : summands c = h :: rest) : lev h = lev c := by
  cases c with
  | zero => simp [summands] at hc
  | plus a b => rw [summands, List.cons.injEq] at hc; rw [← hc.1]; rfl
  | _ => simp only [summands, List.cons.injEq] at hc; rw [hc.1]

theorem lt_of_head_lt {b t h : Tm} {rest : List Tm} (htp : isPrincipal t = true)
    (hs : summands b = h :: rest) (h1 : cmpP h t = .lt) : Lt b t := by
  unfold Lt
  rw [cmp_eq, hs, summands_principal htp, cmpList_cons_cons_ne _ _ (by rw [h1]; decide), h1]

/-- `w ∈ C(g, d)` で、`w` の部分項 `v` について `v < d → v < d'` と `v < g → v < g'` なら
    `w ∈ C(g', d')` -/
theorem inC_mono : ∀ w g d g' d' : Tm, inC w g d = true →
    (∀ v, v ∈ subs w → Lt v d → Lt v d') → (∀ v, v ∈ subs w → Lt v g → Lt v g') →
    inC w g' d' = true := by
  intro w
  induction w with
  | zero => intros; exact inC_zero _ _
  | M n => intros; exact inC_M n _ _
  | plus a b iha ihb =>
    intro g d g' d' h hd hg
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨iha g d g' d' h.1 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv])),
      ihb g d g' d' h.2 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv]))⟩
  | Om e ihe =>
    intro g d g' d' h hd hg
    rw [inC_om] at h ⊢
    exact ihe g d g' d' h (fun v hv => hd v (by simp [subs, hv]))
      (fun v hv => hg v (by simp [subs, hv]))
  | Xi n a iha =>
    intro g d g' d' h hd hg
    rcases inC_xi_iff.mp h with h | ⟨h1, h2⟩
    · exact inC_xi_iff.mpr (Or.inl (hd _ (self_mem_subs _) h))
    · exact inC_xi_iff.mpr (Or.inr ⟨iha g d g' d' h1 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv])), hg a (mem_subs_xi n a) h2⟩)
  | Psi k δ ihk ihδ =>
    intro g d g' d' h hd hg
    rcases inC_psi_iff.mp h with h | ⟨hk, hδ, hlt⟩
    · exact inC_psi_iff.mpr (Or.inl (hd _ (self_mem_subs _) h))
    · refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, hg δ (mem_subs_psi_a k δ) hlt⟩)
      · exact ihk g d g' d' hk (fun v hv => hd v (by simp [subs, hv]))
          (fun v hv => hg v (by simp [subs, hv]))
      · exact ihδ g d g' d' hδ (fun v hv => hd v (by simp [subs, hv]))
          (fun v hv => hg v (by simp [subs, hv]))

theorem exists_max_size : ∀ S : List Tm, S ≠ [] → ∃ t, t ∈ S ∧ ∀ s, s ∈ S → s.size ≤ t.size
  | [], h => absurd rfl h
  | x :: rest, _ => by
    cases rest with
    | nil =>
      exact ⟨x, List.mem_cons_self, fun s hs => by
        rw [List.mem_singleton.mp hs]; exact Nat.le_refl _⟩
    | cons y rest' =>
      obtain ⟨t, ht, hmax⟩ := exists_max_size (y :: rest') (by simp)
      by_cases hxt : t.size ≤ x.size
      · refine ⟨x, List.mem_cons_self, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e | e
        · rw [e]; exact Nat.le_refl _
        · exact Nat.le_trans (hmax s e) hxt
      · refine ⟨t, List.mem_cons_of_mem _ ht, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e | e
        · rw [e]; omega
        · exact hmax s e

theorem length_filter_ne_lt : ∀ {S : List Tm} {t : Tm}, t ∈ S →
    (S.filter (fun s => s != t)).length < S.length
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, t, h => by
    rw [List.filter_cons]
    by_cases e : x = t
    · subst e
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have hx : (x != t) = true := bne_iff_ne.mpr e
      simp only [hx, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm e
      · exact Nat.succ_lt_succ (length_filter_ne_lt h')

theorem not_lt_zero (t : Tm) : ¬ Lt t .zero := by
  unfold Lt
  rw [cmp_eq]
  show ¬ cmpList (summands t) [] = .lt
  cases summands t with
  | nil => rw [cmpList_nil_nil]; decide
  | cons _ _ => rw [cmpList_cons_nil]; decide

theorem zero_lt {t : Tm} (ht : t ≠ .zero) : Lt .zero t := by
  unfold Lt
  rw [cmp_eq]
  show cmpList [] (summands t) = .lt
  cases hs : summands t with
  | nil => exact absurd hs (summands_ne_nil ht)
  | cons _ _ => exact cmpList_nil_cons _ _

/-- `z + 1` -/
def succT : Tm → Tm
  | .zero => one
  | .plus a b => .plus a (succT b)
  | t => .plus t one

theorem summands_succT : ∀ z : Tm, summands (succT z) = summands z ++ [one]
  | .zero => rfl
  | .plus a b => by rw [succT, summands_plus, summands_plus, summands_succT b]; rfl
  | .M _ | .Om _ | .Xi _ _ | .Psi _ _ => rfl

theorem succT_ne_zero (z : Tm) : succT z ≠ .zero := by
  cases z <;> simp [succT, one]

theorem cmpList_append_lt (l m : List Tm) (hm : m ≠ []) : cmpList l (l ++ m) = .lt := by
  induction l with
  | nil =>
    cases m with
    | nil => exact absurd rfl hm
    | cons _ _ => exact cmpList_nil_cons _ _
  | cons x xs ih => rw [List.cons_append, cmpList_cons_cons_eq _ _ (cmpP_self x)]; exact ih

theorem lt_succT (z : Tm) : Lt z (succT z) := by
  unfold Lt
  rw [cmp_eq, summands_succT]
  exact cmpList_append_lt _ _ (by simp)

theorem isSucc_succT (z : Tm) : isSucc (succT z) = true := by
  simp [isSucc, summands_succT]

/-- `Ξ_n` どうしの反対称性と相等 -/
theorem xi_SE {n : Nat} {a b : Tm}
    (hab : cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)) :
    cmpP (.Xi n b) (.Xi n a) = (cmpP (.Xi n a) (.Xi n b)).swap ∧
      (cmpP (.Xi n a) (.Xi n b) = .eq → Tm.Xi n a = .Xi n b) := by
  rw [cmpP_xi_xi, cmpP_xi_xi, xiLtXi_eq, xiLtXi_eq]
  cases eab : cmp a b with
  | eq =>
    have := hab.2 eab
    subst this
    simp
  | lt =>
    have eba : cmp b a = .gt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC a b (Tm.Xi n b) <;> simp
  | gt =>
    have eba : cmp b a = .lt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC b a (Tm.Xi n a) <;> simp

theorem ne_gt_of_le {a b : Tm} (h : Le a b) : cmp a b ≠ .gt := by
  rcases h with rfl | h
  · rw [cmp_self]; decide
  · unfold Lt at h; rw [h]; decide

theorem lt_of_lev_lt' {a b : Tm} (h : lev a < lev b) : Lt a b := by
  have hb0 : b ≠ .zero := by intro e; subst e; simp only [lev] at h; omega
  by_cases ha0 : a = .zero
  · subst ha0
    exact zero_lt hb0
  · cases hsa : summands a with
    | nil => exact absurd hsa (summands_ne_nil ha0)
    | cons x xs =>
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons y ys =>
        unfold Lt
        rw [cmp_eq, hsa, hsb]
        have e : cmpP x y = .lt := cmpP_of_lev_lt (by rw [lev_head hsa, lev_head hsb]; exact h)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem lev_le_of_lt_gen {w y : Tm} (h : Lt w y) : lev w ≤ lev y := by
  apply Nat.le_of_not_lt
  intro hl
  have hw0 : w ≠ .zero := by intro e; subst e; simp only [lev] at hl; omega
  by_cases hy0 : y = .zero
  · subst hy0; exact not_lt_zero w h
  · cases hsw : summands w with
    | nil => exact absurd hsw (summands_ne_nil hw0)
    | cons x xs =>
      cases hsy : summands y with
      | nil => exact absurd hsy (summands_ne_nil hy0)
      | cons z zs =>
        unfold Lt at h
        rw [cmp_eq, hsw, hsy] at h
        have e : cmpP x z = .gt := cmpP_of_lev_gt (by rw [lev_head hsw, lev_head hsy]; exact hl)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h
        cases h

/-- `M_n` 以上の項は階 `n` の項より小さくない -/
theorem not_lt_of_not_lt_M {n : Nat} {w y : Tm} (hy : lev y = n)
    (h : ¬ Lt w (.M n)) : ¬ Lt w y := by
  intro h'
  have hl := lev_le_of_lt_gen h'
  exact h (lt_of_lev_lt' (by simp only [lev]; omega))

/-- 主要項 `t` より小さい和は、先頭の項も `t` より小さい -/
theorem cmpP_head_of_lt {w h t : Tm} {rest : List Tm} (hs : summands w = h :: rest)
    (htp : isPrincipal t = true) (hlt : Lt w t) : cmpP h t = .lt := by
  unfold Lt at hlt
  rw [cmp_eq, hs, summands_principal htp] at hlt
  rcases cmpList_lt_cases hlt with e | ⟨_, e⟩
  · exact e
  · cases rest with
    | nil => rw [cmpList_nil_nil] at e; cases e
    | cons _ _ => rw [cmpList_cons_nil] at e; cases e

theorem lt_plus_plus_same {a b b' : Tm} : Lt (.plus a b) (.plus a b') ↔ Lt b b' := by
  unfold Lt
  rw [cmp_eq, cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]

theorem size_induction {P : Tm → Prop} (h : ∀ t, (∀ s, s.size < t.size → P s) → P t)
    (t : Tm) : P t := by
  have key : ∀ n, ∀ t : Tm, t.size < n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | succ n ih => intro t ht; exact h t (fun s hs => ih s (by omega))
  exact key _ t (Nat.lt_succ_self _)

/-- 有限の一覧の上の「全ては成り立たない」から反例を取り出す -/
theorem exists_of_not_forall_mem {P : Tm → Prop} [DecidablePred P] :
    ∀ l : List Tm, ¬ (∀ w, w ∈ l → P w) → ∃ w, w ∈ l ∧ ¬ P w
  | [], h => absurd (fun _ hw => absurd hw List.not_mem_nil) h
  | x :: xs, h => by
    by_cases hx : P x
    · obtain ⟨w, hw, hP⟩ := exists_of_not_forall_mem xs (fun h' => h (fun w hw => by
        rcases List.mem_cons.mp hw with e | e
        · subst e; exact hx
        · exact h' w e))
      exact ⟨w, List.mem_cons_of_mem _ hw, hP⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

/-! ### 前線 -/

/-- 項 `R` についての前線：`x` の `R` 未満の極大の崩壊の節点 -/
def fr (R : Tm) : Tm → List Tm
  | .plus a b => fr R a ++ fr R b
  | .Om a => fr R a
  | .Xi m a => if Lt (.Xi m a) R then [.Xi m a] else fr R a
  | .Psi p a => if Lt (.Psi p a) R then [.Psi p a] else fr R p ++ fr R a
  | _ => []

/-- 前線の元は部分項で `R` 未満 -/
theorem fr_spec {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x → w ∈ subs x ∧ Lt w R
  | .zero, _, h | .M _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact ⟨subs_plus_l (fr_spec h).1, (fr_spec h).2⟩
    · exact ⟨subs_plus_r (fr_spec h).1, (fr_spec h).2⟩
  | .Om a, w, h => by
    rw [fr] at h
    exact ⟨subs_om (fr_spec h).1, (fr_spec h).2⟩
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte] at h
      exact ⟨subs_xi (fr_spec h).1, (fr_spec h).2⟩
  | .Psi p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with h | h
      · exact ⟨subs_psi_p (fr_spec h).1, (fr_spec h).2⟩
      · exact ⟨subs_psi_a (fr_spec h).1, (fr_spec h).2⟩

/-- 前線による `C` への所属の言い換え：`R` 以上の節点が `d` 未満でなく、その引数が `g0` 未満
    （したがって `g` 未満）なら、`x ∈ C(g, d)` は前線の各節点が `C(g, d)` に入ることと同値 -/
theorem inC_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true)
  | .zero, _, _, _ => by simp [fr, inC_zero]
  | .M n, _, _, _ => by simp [fr, inC_M]
  | .plus a b, h0, hd, hg => by
    rw [inC_plus, Bool.and_eq_true] at h0
    rw [inC_plus, Bool.and_eq_true, fr]
    rw [inC_fr a h0.1 (fun w hw => hd w (subs_plus_l hw)) (fun v hv => hg v (subs_plus_l hv)),
      inC_fr b h0.2 (fun w hw => hd w (subs_plus_r hw)) (fun v hv => hg v (subs_plus_r hv))]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ w (hw | hw)
      · exact h1 w hw
      · exact h2 w hw
    · intro h
      exact ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩
  | .Om a, h0, hd, hg => by
    rw [inC_om] at h0
    rw [inC_om, fr]
    exact inC_fr a h0 (fun w hw => hd w (subs_om hw)) (fun v hv => hg v (subs_om hv))
  | .Xi m a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_xi m a) hlt
      rw [inC_xi_iff, ← inC_fr a ha (fun w hw => hd w (subs_xi hw)) (fun v hv => hg v (subs_xi hv))]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact absurd h hnd
        · exact h
      · intro h
        exact Or.inr ⟨h, hag⟩
  | .Psi p a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Psi p a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_psi_iff.mp h0 with h | ⟨hp, ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_psi_a p a) hlt
      rw [inC_psi_iff,
        inC_fr p hp (fun w hw => hd w (subs_psi_p hw)) (fun v hv => hg v (subs_psi_p hv)),
        inC_fr a ha (fun w hw => hd w (subs_psi_a hw)) (fun v hv => hg v (subs_psi_a hv))]
      simp only [List.mem_append]
      constructor
      · rintro (h | ⟨h1, h3, _⟩)
        · exact absurd h hnd
        · rintro w (hw | hw)
          · exact h1 w hw
          · exact h3 w hw
      · intro h
        exact Or.inr ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw), hag⟩

/-- 前線の元は `Ξ` か `Ψ` の節点 -/
theorem fr_node {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x →
    (∃ m a, w = .Xi m a) ∨ (∃ p a, w = .Psi p a)
  | .zero, _, h | .M _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_node h
    · exact fr_node h
  | .Om a, w, h => by rw [fr] at h; exact fr_node h
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl ⟨m, a, h⟩
    · simp only [hR, ↓reduceIte] at h
      exact fr_node h
  | .Psi p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inr ⟨p, a, h⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with h | h
      · exact fr_node h
      · exact fr_node h

theorem inC_of_lt_node {w g d : Tm} (hw : (∃ m a, w = .Xi m a) ∨ (∃ p a, w = .Psi p a))
    (h : Lt w d) : inC w g d = true := by
  rcases hw with ⟨m, a, rfl⟩ | ⟨p, a, rfl⟩
  · exact inC_xi_iff.mpr (Or.inl h)
  · exact inC_psi_iff.mpr (Or.inl h)

/-- 前線の各節点が `C(g, d)` に入ることは、崩壊の性質があれば `d` 未満と同値 -/
theorem fr_inC_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (∀ w, w ∈ fr R x → inC w g d = true) ↔ (∀ w, w ∈ fr R x → Lt w d) :=
  ⟨fun h w hw => hcoll w hw (h w hw), fun h w hw => inC_of_lt_node (fr_node hw) (h w hw)⟩

theorem fr_inC_false_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (¬ ∀ w, w ∈ fr R x → inC w g d = true) ↔ (∃ w, w ∈ fr R x ∧ ¬ Lt w d) := by
  rw [fr_inC_iff hcoll]
  constructor
  · exact exists_of_not_forall_mem _
  · rintro ⟨w, hw, hn⟩ h
    exact hn (h w hw)

theorem fr_mem_plus_l {R a b w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inl h

theorem fr_mem_plus_r {R a b w : Tm} (h : w ∈ fr R b) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inr h

theorem fr_mem_om {R a w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.Om a) := by
  rw [fr]; exact h

theorem fr_mem_xi {R a w : Tm} {n : Nat} (hn : ¬ Lt (.Xi n a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hn, ↓reduceIte]; exact h

theorem fr_mem_xi_self {R a : Tm} {n : Nat} (hl : Lt (.Xi n a) R) :
    Tm.Xi n a ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

theorem fr_mem_psi_p {R p a w : Tm} (hn : ¬ Lt (.Psi p a) R) (h : w ∈ fr R p) :
    w ∈ fr R (.Psi p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl h

theorem fr_mem_psi_a {R p a w : Tm} (hn : ¬ Lt (.Psi p a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Psi p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inr h

theorem fr_mem_psi_self {R p a : Tm} (hl : Lt (.Psi p a) R) :
    Tm.Psi p a ∈ fr R (.Psi p a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

/-- `t` は `S` を切断する -/
def CutT (S : List Tm) (t : Tm) : Prop :=
  ∀ a b, a ∈ S → b ∈ S → Lt b a → Lt a t → Lt b t

/-- 部分項の大きさの比較 -/
macro "size_omega" : tactic =>
  `(tactic| first | (simp only [Tm.size]; omega) | (simp only [Tm.size] at *; omega))

end MahloOCF

/-! ## 標準形の分解 -/

namespace MahloOCF

open Tm

/-- 標準形 -/
def WNF (t : Tm) : Prop := isNF t = true

/-- `Ψ` の崩壊先：`Ω_0`、`Ω_c`（`c` は後者）、`Ξ_n(p)` -/
def IsTgt (π : Tm) : Prop :=
  π = .Om .zero ∨ (∃ c, π = .Om c ∧ isSucc c = true) ∨ (∃ n p, π = .Xi n p)

theorem isTgt_of_isRegTerm {π : Tm} (h : isRegTerm π = true) : IsTgt π := by
  cases π with
  | Om c =>
    simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨c, rfl, h⟩)
  | Xi n p => exact Or.inr (Or.inr ⟨n, p, rfl⟩)
  | _ => simp [isRegTerm] at h

theorem IsTgt.isRegTerm {π : Tm} (h : IsTgt π) : isRegTerm π = true := by
  rcases h with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
  · rfl
  · show (c == zero || isSucc c) = true
    rw [hs, Bool.or_true]
  · rfl

theorem WNF.plus {a b : Tm} (h : WNF (.plus a b)) :
    WNF a ∧ WNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  have hn : isNF (.plus a b) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  exact ⟨hn.1.1.2, hn.1.2, hn.1.1.1.1, hn.1.1.1.2⟩

theorem WNF.plus_head {a b : Tm} (h : WNF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn : isNF (.plus a b) = true := h
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

theorem WNF.om {a : Tm} (h : WNF (.Om a)) : WNF a ∧ omegaFixed a = false := by
  have hn : isNF (.Om a) = true := h
  simp only [isNF, Bool.and_eq_true, Bool.not_eq_true'] at hn
  exact hn

theorem WNF.xi {n : Nat} {a : Tm} (h : WNF (.Xi n a)) :
    1 ≤ n ∧ WNF a ∧ cmp a (succM n) ≠ .gt ∧ inC a a (.M n) = true := by
  have hn : isNF (.Xi n a) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  exact ⟨hn.1.1.1, hn.1.1.2, hn.1.2, hn.2⟩

/-- `Ψ_π(a)` の標準形の条件 -/
structure PsiNF (pi a : Tm) : Prop where
  tgt : IsTgt pi
  piF : WNF pi
  aF : WNF a
  /-- `π = Ξ_m(d)` なら `d < a` -/
  act : ∀ m d, pi = .Xi m d → Lt d a
  /-- `a ∈ C(a, Ψ_π(a))` -/
  Ca : inC a a (.Psi pi a) = true

theorem WNF.psi {pi a : Tm} (h : WNF (.Psi pi a)) : PsiNF pi a := by
  have hn : isNF (.Psi pi a) = true := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨hpin, han⟩, hreg⟩, hact⟩, hC⟩ := hn
  refine ⟨isTgt_of_isRegTerm hreg, hpin, han, ?_, hC⟩
  intro m d e
  subst e
  simp only [MahloOCF.lt, beq_iff_eq] at hact
  exact hact

theorem WNF.mk_psi {pi a : Tm} (h : PsiNF pi a) : WNF (.Psi pi a) := by
  show isNF (.Psi pi a) = true
  simp only [isNF, Bool.and_eq_true]
  refine ⟨⟨⟨⟨h.piF, h.aF⟩, h.tgt.isRegTerm⟩, ?_⟩, h.Ca⟩
  cases pi with
  | Xi m d =>
    simp only [MahloOCF.lt, beq_iff_eq]
    exact h.act m d rfl
  | _ => rfl

theorem WNF.M {n : Nat} (h : WNF (.M n)) : 1 ≤ n := by
  have hn : isNF (.M n) = true := h
  simp only [isNF, decide_eq_true_eq] at hn
  exact hn

theorem WNF.zero : WNF .zero := rfl

theorem WNF.M' {n : Nat} (h : 1 ≤ n) : WNF (.M n) := by
  show isNF (.M n) = true
  simp only [isNF, decide_eq_true_eq]
  exact h

theorem WNF.om_zero : WNF (.Om .zero) := rfl

theorem WNF.one : WNF one :=
  WNF.mk_psi ⟨Or.inl rfl, WNF.om_zero, WNF.zero, (fun _ _ h => by cases h), inC_zero _ _⟩

theorem summands_WNF : ∀ t : Tm, WNF t → ∀ s, s ∈ summands t → WNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_WNF b hb s hs
  | .M _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs | .Psi _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem WNF.of_mem_subs : ∀ {t s : Tm}, WNF t → s ∈ subs t → WNF s
  | .zero, s, ht, h | .M _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ha h
    · exact WNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.xi.2.1 h
  | .Psi p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hP := ht.psi
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs hP.piF h
    · exact WNF.of_mem_subs hP.aF h

theorem WNF.mk_plus {a b : Tm} (ha : WNF a) (hb : WNF b) (hap : isPrincipal a = true)
    (hb0 : b ≠ .zero) (hh : ∀ h rest, summands b = h :: rest → cmp h a ≠ .gt) :
    WNF (.plus a b) := by
  show isNF (.plus a b) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨hap, hb0⟩, ha⟩, hb⟩, ?_⟩
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons h rest =>
    have := hh h rest hs
    simpa using this

/-! ### 和 -/

theorem lt_plus_leftY {a b : Tm} (h : WNF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal hap, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

/-- 主要項 `y` について `a + b < y` ⟺ `a < y` -/
theorem lt_plus_prin_iffY {a b y : Tm} (h : WNF (.plus a b)) (hyp : isPrincipal y = true) :
    Lt (.plus a b) y ↔ Lt a y := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  rw [lt_principal_iff hap hyp]
  unfold Lt
  rw [cmp_eq, summands_principal hyp, summands_plus]
  cases e : cmpP a y with
  | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
  | eq =>
    rw [cmpList_cons_cons_eq _ _ e]
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons _ _ => rw [cmpList_cons_nil]; simp
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

/-- 主要項 `x` より小さい項は `x + y` より小さい -/
theorem lt_plus_of_lt_prin {e x y : Tm} (hxp : isPrincipal x = true) (h : Lt e x) :
    Lt e (.plus x y) := by
  unfold Lt at h ⊢
  rw [cmp_eq, summands_principal hxp] at h
  rw [cmp_eq, summands_plus]
  cases hs : summands e with
  | nil => exact cmpList_nil_cons _ _
  | cons z zs =>
    rw [hs] at h
    rcases cmpList_lt_cases h with e1 | ⟨e1, e2⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · cases zs with
      | nil => rw [cmpList_nil_nil] at e2; cases e2
      | cons _ _ => rw [cmpList_cons_nil] at e2; cases e2

/-- 先頭の項は和以下 -/
theorem head_leY {t h : Tm} {rest : List Tm} (ht : WNF t) (hs : summands t = h :: rest) :
    Le h t := by
  cases t with
  | zero => simp [summands] at hs
  | plus a b =>
    rw [summands_plus, List.cons.injEq] at hs
    rw [← hs.1]
    exact Or.inr (lt_plus_leftY ht)
  | _ =>
    simp only [summands, List.cons.injEq] at hs
    rw [hs.1]
    exact Le.refl _

/-! ### 階 -/

theorem lev_posY : ∀ {t : Tm}, WNF t → t ≠ .zero → 1 ≤ lev t
  | .zero, _, h => absurd rfl h
  | .M _, _, _ => by simp only [lev]; omega
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    show 1 ≤ lev a
    exact lev_posY ha this
  | .Om a, _, _ => by simp only [lev]; omega
  | .Xi _ _, ht, _ => ht.xi.1
  | .Psi pi _, ht, _ => by
    have hP := ht.psi
    show 1 ≤ lev pi
    rcases hP.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · simp only [lev]; omega
    · simp only [lev]; omega
    · exact hP.piF.xi.1

/-- 底（同じ階の最小元）：`M_n` -/
def isBot : Tm → Bool
  | .M _ => true
  | _ => false

/-- 底より小さい同じ階の項はない -/
theorem not_lt_isBotY {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : WNF x)
    (hyF : WNF y) : cmpP x y ≠ .lt := by
  cases y with
  | M n =>
    rw [cmpP.eq_def]
    simp only [hl, Nat.lt_irrefl, ↓reduceIte]
    cases x with
    | M m => simp
    | Om b =>
      simp only [beq_iff_eq]
      split <;> simp
    | zero => simp only [lev] at hl; omega
    | _ => simp
  | _ => simp [isBot] at hy

/-- `x < M_n` なら `x` の階は `n` 以下 -/
theorem lev_le_of_lt_MY {z : Tm} {n : Nat} (hn : 1 ≤ n) (hz : WNF z) (h : Lt z (.M n)) :
    lev z ≤ n := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_WNF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.M n) = [.M n] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; omega
      · exact absurd e (not_lt_isBotY (by simp only [lev]; exact h1) rfl hx.1 (WNF.M' hn))
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- `x < M_n` ⟺ `x` の階が `n` 以下 -/
theorem lt_M_iffY {x : Tm} {m : Nat} (hx : WNF x) (hm : 1 ≤ m) : Lt x (.M m) ↔ lev x ≤ m :=
  ⟨lev_le_of_lt_MY hm hx, fun h => lt_of_lev_lt' (by simp only [lev]; omega)⟩

end MahloOCF

/-! ## 順序の性質を仮定せずに成り立つ比較の展開 -/

namespace MahloOCF

open Tm

/-- `Ω` の不動点になる（底でない）主要項：`Ξ_n(a)` と `Ψ_{Ξ_n(p)}(β)` -/
def IsOF (X : Tm) : Prop :=
  (∃ n a, X = .Xi n a) ∨ ∃ n p β, X = .Psi (.Xi n p) β

theorem IsOF.principal {X : Tm} (h : IsOF X) : isPrincipal X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> rfl

theorem IsOF.fixed {X : Tm} (h : IsOF X) : omegaFixed X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> rfl

theorem IsOF.not_bot {X : Tm} (h : IsOF X) : isBot X = false := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> rfl

theorem IsOF.ne_zero {X : Tm} (h : IsOF X) : X ≠ .zero := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> intro e <;> cases e

theorem IsOF.lev_pos {X : Tm} (h : IsOF X) (hX : WNF X) : 1 ≤ lev X :=
  lev_posY hX h.ne_zero

theorem cmpOmX_OF {a X : Tm} (hX : IsOF X) : cmpOmX a X = cmp a X := by
  rw [cmpOmX.eq_def]
  simp [hX.fixed]

theorem cmpP_om_OF {e X : Tm} (hX : IsOF X) (hl : max 1 (lev e) = lev X) :
    cmpP (.Om e) X = cmp e X := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩
  · exact cmpP_om_xi hl
  · exact cmpP_om_psiXi hl

theorem cmpP_OF_om {e X : Tm} (hX : IsOF X) (hl : max 1 (lev e) = lev X) :
    cmpP X (.Om e) = (cmp e X).swap := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩
  · exact cmpP_xi_om hl
  · exact cmpP_psiXi_om hl

/-- `Ω` の不動点 `X` と `Ω_e`：`Ω_e < X` ⟺ `e < X` -/
theorem lt_om_OFG {e X : Tm} (hX : IsOF X) (hXF : WNF X) :
    Lt (.Om e) X ↔ Lt e X := by
  have hX1 := hX.lev_pos hXF
  rcases Nat.lt_trichotomy (max 1 (lev e)) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' (by omega), fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

/-! ### 主要項の形 -/

/-- 底でない主要項の形 -/
theorem shape_prin {x : Tm} (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ n a, x = .Xi n a) ∨ (∃ π β, x = .Psi π β) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Xi n a => exact Or.inr (Or.inl ⟨n, a, rfl⟩)
  | Psi π β => exact Or.inr (Or.inr ⟨π, β, rfl⟩)
  | _ => simp_all [isPrincipal, isBot]

/-- 崩壊先の形 -/
theorem WNF.psi_shape {π β : Tm} (h : WNF (.Psi π β)) :
    π = .Om .zero ∨ (∃ c, π = .Om c ∧ isSucc c = true) ∨ (∃ n p, π = .Xi n p) :=
  h.psi.tgt

/-- 底でない主要項の、`Ω` の不動点で分けた形 -/
theorem shape_prinOF {x : Tm} (hx : WNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ IsOF x ∨ (∃ c β, x = .Psi (.Om c) β) := by
  rcases shape_prin hp hb with ⟨a, rfl⟩ | ⟨n, a, rfl⟩ | ⟨π, β, rfl⟩
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl (Or.inl ⟨n, a, rfl⟩))
  · rcases hx.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact Or.inr (Or.inr ⟨.zero, β, rfl⟩)
    · exact Or.inr (Or.inr ⟨c, β, rfl⟩)
    · exact Or.inr (Or.inl (Or.inr ⟨n, p, β, rfl⟩))

/-! ### `Ψ_{Ω_c}` と `Ω` -/

theorem lt_om_psiOm (a c β : Tm) (hl : max 1 (lev a) = max 1 (lev c)) :
    Lt (.Om a) (.Psi (.Om c) β) ↔ Lt a c := by
  rw [lt_principal_iff rfl rfl, cmpP_om_psiOm hl]
  unfold Lt
  by_cases h : cmp a c = .lt <;> simp [h]

theorem lt_psiOm_om (a c β : Tm) (hl : max 1 (lev a) = max 1 (lev c)) :
    Lt (.Psi (.Om c) β) (.Om a) ↔ ¬ Lt a c := by
  rw [lt_principal_iff rfl rfl, cmpP_psiOm_om hl]
  unfold Lt
  by_cases h : cmp a c = .lt <;> simp [h]

theorem lt_psiOm_om_self (c δ : Tm) : Lt (.Psi (.Om c) δ) (.Om c) :=
  (lt_psiOm_om c c δ rfl).mpr (Lt.irrefl c)

/-! ### `Ψ` と `Ξ` -/

/-- 同じ階の `Ψ_π(a)` と `Ξ_n(b)` の比較 -/
theorem lt_psi_xiY {π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Psi π a) (.Xi n b) ↔
      cmp π (.Xi n b) ≠ .gt ∨ baseOf (.Xi n b) (.Psi π a) = false := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_xi hl, psiLtXi_eq, ite_lt_gt_eq_lt]
  cases cmp π (Tm.Xi n b) <;> cases baseOf (Tm.Xi n b) (Tm.Psi π a) <;> simp

theorem lt_xi_psiY {π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Xi n b) (.Psi π a) ↔ ¬ Lt (.Psi π a) (.Xi n b) := by
  rw [lt_principal_iff rfl rfl, lt_principal_iff rfl rfl, cmpP_xi_psi hl, cmpP_psi_xi hl]
  cases psiLtXi (Tm.Psi π a) (.Xi n b) <;> simp

/-- 崩壊先より小さい -/
theorem lt_psi_targetY {π a : Tm} (h : WNF (.Psi π a)) : Lt (.Psi π a) π := by
  rcases h.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
  · exact lt_psiOm_om_self _ a
  · exact lt_psiOm_om_self c a
  · exact (lt_psi_xiY (π := .Xi n p) (n := n) rfl).mpr (Or.inl (by rw [cmp_self]; decide))

/-! ### `Ψ` どうし -/

/-- 同じ階の `Ψ` どうしの比較の展開 -/
theorem lt_psi_psiY {π a σ b : Tm} (hl : lev π = lev σ) :
    Lt (.Psi π a) (.Psi σ b) ↔
      (π = σ ∧ Lt a b) ∨ (π ≠ σ ∧ Lt σ π ∧ baseOf σ (.Psi π a) = false) ∨
        (π ≠ σ ∧ ¬ Lt σ π ∧ baseOf π (.Psi σ b) = true) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_psi hl, cmpPsi_eq]
  unfold Lt
  by_cases e : π = σ
  · subst e; simp
  · simp only [e, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and, false_or]
    by_cases h : cmp σ π = .lt
    · simp only [h, ↓reduceIte, not_true_eq_false, false_and, or_false]
      cases baseOf σ (Tm.Psi π a) <;> simp
    · simp only [h, ↓reduceIte, false_and, false_or, not_false_eq_true, true_and]
      cases baseOf π (Tm.Psi σ b) <;> simp

/-- 同じ崩壊先の `Ψ` は引数で比べる -/
theorem lt_psi_psi_same {π a b : Tm} : Lt (.Psi π a) (.Psi π b) ↔ Lt a b := by
  rw [lt_psi_psiY rfl]
  simp

/-! ### 底の条件 -/

theorem baseOf_om_zero (t : Tm) : baseOf (.Om .zero) t = true ↔ t ≠ .zero := by
  rw [baseOf_om]
  simp [isSucc, summands]

theorem baseOf_om_succ {c t : Tm} (hs : isSucc c = true) :
    baseOf (.Om c) t = true ↔ Lt (omOf (predT c)) t := by
  rw [baseOf_om]
  simp only [hs, ↓reduceIte, beq_iff_eq]
  rfl

theorem baseOf_xi_iff (m : Nat) (d t : Tm) :
    baseOf (.Xi m d) t = true ↔ Lt (kTerm (m - 1)) t ∧ inC d d t = true := by
  rw [baseOf_xi]
  simp only [Bool.and_eq_true, beq_iff_eq]
  rfl

theorem Lt.ne_zero {a b : Tm} (h : Lt a b) : b ≠ .zero := by
  intro e; subst e; exact not_lt_zero a h

end MahloOCF

/-! ## `1` と `predT`（順序の仮定なし） -/

namespace MahloOCF

open Tm

theorem lev_one : lev one = 1 := rfl

theorem summands_one : summands one = [one] := rfl

theorem cmp_zero_left (b : Tm) : cmp .zero b = .lt ∨ (cmp .zero b = .eq ∧ b = .zero) := by
  by_cases hb : b = .zero
  · subst hb; right; exact ⟨cmp_self _, rfl⟩
  · left; exact zero_lt hb

/-- `1` は和でない 0 以外の標準形以下 -/
theorem cmpP_one_ne_gt {z : Tm} (hz : WNF z) (hp : isPrincipal z = true) : cmpP one z ≠ .gt := by
  have hz0 : z ≠ .zero := by intro e; subst e; simp [isPrincipal] at hp
  have hl : 1 ≤ lev z := lev_posY hz hz0
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by rw [lev_one]; exact hl)]; decide
  · cases z with
    | zero => exact absurd rfl hz0
    | plus _ _ => simp [isPrincipal] at hp
    | M m => exact absurd hz.M (by simp only [lev] at hl; omega)
    | Om a =>
      unfold one
      rw [cmpP_psiOm_om (by simp only [lev] at hl ⊢; omega)]
      have : ¬ cmp a .zero = .lt := not_lt_zero a
      simp [this]
    | Xi n b =>
      have hn : n = 1 := by simp only [lev] at hl; omega
      subst hn
      unfold one
      rw [cmpP_psi_xi (pi := .Om .zero) (m := 1) rfl, psiLtXi_eq]
      have h1 : cmp (Tm.Om .zero) (.Xi 1 b) = .lt := by
        rw [cmp_principal rfl rfl, cmpP_om_xi (a := .zero) (n := 1) rfl]
        exact zero_lt (by intro e; cases e)
      simp [h1]
    | Psi π b =>
      unfold one
      rw [cmpP_psi_psi (by simp only [lev] at hl ⊢; omega), cmpPsi_eq]
      by_cases e : Tm.Om .zero = π
      · subst e
        simp only [↓reduceIte]
        rcases cmp_zero_left b with h | ⟨h, -⟩ <;> rw [h] <;> decide
      · simp only [e, ↓reduceIte]
        have hb : baseOf (Tm.Om .zero) (Tm.Psi π b) = true :=
          (baseOf_om_zero _).mpr (by intro h; cases h)
        have hπ : ¬ cmp π (Tm.Om .zero) = .lt := by
          rcases hz.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨n, d, rfl⟩
          · exact absurd rfl e
          · intro h
            rw [cmp_principal rfl rfl] at h
            by_cases hl2 : 1 < max 1 (lev c)
            · rw [cmpP_of_lev_gt (by simp only [lev]; omega)] at h; cases h
            · rw [cmpP_om_om (by simp only [lev]; omega)] at h
              exact not_lt_zero c h
          · intro h
            have hn : n = 1 := by simp only [lev] at hl; omega
            subst hn
            rw [cmp_principal rfl rfl, cmpP_xi_om (a := .zero) (n := 1) rfl,
              zero_lt (t := Tm.Xi 1 d) (by intro e; cases e)] at h
            cases h
        simp only [hπ, ↓reduceIte, hb]; decide

/-- `cmpP 1 z = .eq` なら `z = 1` -/
theorem eq_one_of_cmpP_eq {z : Tm} (hp : isPrincipal z = true) (h : cmpP one z = .eq) :
    z = one := by
  unfold one at h
  by_cases hl : lev (Tm.Psi (.Om .zero) .zero) < lev z
  · rw [cmpP_of_lev_lt hl] at h; cases h
  by_cases hl' : lev z < lev (Tm.Psi (.Om .zero) .zero)
  · rw [cmpP_of_lev_gt hl'] at h; cases h
  have hl1 : lev z = 1 := by simp only [lev] at hl hl' ⊢; omega
  cases z with
  | zero => simp only [lev] at hl1; omega
  | plus a b => simp [isPrincipal] at hp
  | M m =>
    have hm : m = 0 := by simp only [lev] at hl1; omega
    subst hm
    rw [cmpP.eq_def] at h
    simp only [lev] at h
    cases h
  | Om a =>
    rw [cmpP_psiOm_om (by simp only [lev] at hl1 ⊢; omega)] at h
    split at h <;> cases h
  | Xi n b =>
    have hn : n = 1 := hl1
    subst hn
    rw [cmpP_psi_xi (pi := .Om .zero) (m := 1) rfl] at h
    split at h <;> cases h
  | Psi π b =>
    rw [cmpP_psi_psi (by simp only [lev] at hl1 ⊢; omega)] at h
    obtain ⟨rfl, h2⟩ := cmpPsi_eq_eq' h
    rcases cmp_zero_left b with h' | ⟨-, rfl⟩
    · rw [h'] at h2; cases h2
    · rfl
where
  cmpPsi_eq_eq' {π γ σ β : Tm} (h : cmpPsi (.Psi π γ) (.Psi σ β) = .eq) :
      π = σ ∧ cmp γ β = .eq := by
    rw [cmpPsi_eq] at h
    by_cases e : π = σ
    · simp only [e, ↓reduceIte] at h
      exact ⟨e, h⟩
    · simp only [e, ↓reduceIte] at h
      split at h
      · split at h <;> cases h
      · split at h <;> cases h

/-- 主要項の列の和 -/
theorem summands_ofSummands : ∀ (l : List Tm), (∀ s, s ∈ l → isPrincipal s = true) →
    summands (ofSummands l) = l
  | [], _ => rfl
  | [a], h => summands_principal (h a List.mem_cons_self)
  | a :: b :: rest, h => by
    show a :: summands (ofSummands (b :: rest)) = a :: b :: rest
    rw [summands_ofSummands (b :: rest) (fun s hs => h s (List.mem_cons_of_mem _ hs))]

theorem summands_principal_of_WNF {c : Tm} (hc : WNF c) : ∀ s, s ∈ summands c →
    isPrincipal s = true := fun s hs => (summands_WNF c hc s hs).2

/-- `c = ζ + 1` の `ζ` の加数 -/
theorem summands_predT {c : Tm} (hc : WNF c) {ys : List Tm} (hys : summands c = ys ++ [one]) :
    summands (predT c) = ys := by
  rw [predT_of_summands hys]
  apply summands_ofSummands
  intro s hs
  exact summands_principal_of_WNF hc s (by rw [hys]; exact List.mem_append_left _ hs)

/-- `ζ < ζ + 1` -/
theorem lt_predT {c : Tm} (hc : WNF c) (hs : isSucc c = true) : Lt (predT c) c := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  unfold Lt
  rw [cmp_eq, summands_predT hc hys, hys]
  exact cmpList_append_lt _ _ (by simp)

/-- 辞書式：`l ++ [1] ≤ m` なら `l < m` -/
theorem cmpList_lt_of_append_one_ne_gt : ∀ (l m : List Tm),
    cmpList (l ++ [one]) m ≠ .gt → cmpList l m = .lt
  | [], [], h => by simp [cmpList_cons_nil] at h
  | [], _ :: _, _ => cmpList_nil_cons _ _
  | _ :: _, [], h => by rw [List.cons_append, cmpList_cons_nil] at h; exact absurd rfl h
  | x :: xs, y :: ys, h => by
    rw [List.cons_append] at h
    cases e : cmpP x y with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e] at h ⊢
      exact cmpList_lt_of_append_one_ne_gt xs ys h
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; exact absurd rfl h

/-- 辞書式：`l < m`（`m` は主要項の標準形の列）なら `l ++ [1] ≤ m` -/
theorem cmpList_append_one_ne_gt : ∀ (l m : List Tm),
    (∀ y, y ∈ m → WNF y ∧ isPrincipal y = true) →
    cmpList l m = .lt → cmpList (l ++ [one]) m ≠ .gt
  | [], [], _, h => by rw [cmpList_nil_nil] at h; cases h
  | [], y :: ys, hm, _ => by
    have hy := hm y List.mem_cons_self
    rw [List.nil_append]
    cases e : cmpP one y with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e]
      cases ys with
      | nil => rw [cmpList_nil_nil]; decide
      | cons _ _ => rw [cmpList_nil_cons]; decide
    | gt => exact absurd e (cmpP_one_ne_gt hy.1 hy.2)
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hm, h => by
    rw [List.cons_append]
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    · rw [cmpList_cons_cons_eq _ _ e]
      exact cmpList_append_one_ne_gt xs ys (fun y hy => hm y (List.mem_cons_of_mem _ hy)) e'

/-- `ζ < d` ⟺ `ζ + 1 ≤ d` -/
theorem lt_predT_iff {c d : Tm} (hc : WNF c) (hs : isSucc c = true) (hd : WNF d) :
    Lt (predT c) d ↔ cmp c d ≠ .gt := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  unfold Lt
  rw [cmp_eq, cmp_eq, summands_predT hc hys, hys]
  exact ⟨cmpList_append_one_ne_gt ys _ (summands_WNF d hd),
    cmpList_lt_of_append_one_ne_gt ys _⟩

/-- 主要項 `x`（`1` でない）について `ζ + 1 < x` ⟺ `ζ < x` -/
theorem lt_succ_prin_iff {c x : Tm} (hc : WNF c) (hs : isSucc c = true)
    (hxp : isPrincipal x = true) (hx1 : x ≠ one) (hxF : WNF x) :
    Lt c x ↔ Lt (predT c) x := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  unfold Lt
  rw [cmp_eq, cmp_eq, summands_predT hc hys, hys, summands_principal hxp]
  cases ys with
  | nil =>
    simp only [List.nil_append]
    rw [cmpList_nil_cons]
    simp only [iff_true]
    cases e : cmpP one x with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    | eq => exact absurd (eq_one_of_cmpP_eq hxp e) hx1
    | gt => exact absurd e (cmpP_one_ne_gt hxF hxp)
  | cons y ys =>
    rw [List.cons_append]
    cases e : cmpP y x with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e,
        cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e, cmpList_cons_cons_eq _ _ e]
      cases ys with
      | nil => rw [List.nil_append, cmpList_cons_nil, cmpList_nil_nil]; simp
      | cons _ _ => rw [List.cons_append, cmpList_cons_nil, cmpList_cons_nil]
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e,
        cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

/-- `ζ` が主要項なら `c = ζ + 1` の先頭の加数 -/
theorem predT_mem_summands {c : Tm} (hc : WNF c) (hs : isSucc c = true)
    (hp : isPrincipal (predT c) = true) : predT c ∈ summands c := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have h1 := summands_predT hc hys
  rw [summands_principal hp] at h1
  rw [hys, ← h1]
  simp

/-- 標準形の加数の列の先頭部分の和は標準形 -/
theorem WNF_ofSummands_prefix : ∀ (t : Tm) (l rest : List Tm), WNF t → summands t = l ++ rest →
    WNF (ofSummands l) := by
  intro t
  induction t with
  | plus a b _ ihb =>
    intro l rest ht hst
    obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
    rw [summands_plus] at hst
    cases l with
    | nil => exact WNF.zero
    | cons x l' =>
      rw [List.cons_append, List.cons.injEq] at hst
      obtain ⟨e1, hst⟩ := hst
      subst e1
      cases l' with
      | nil => exact ha
      | cons y l'' =>
        have hb' := ihb (y :: l'') rest hb hst
        have hprin : ∀ s, s ∈ y :: l'' → isPrincipal s = true := fun s hs =>
          (summands_WNF b hb s (by rw [hst]; exact List.mem_append_left _ hs)).2
        show WNF (.plus a (ofSummands (y :: l'')))
        refine WNF.mk_plus ha hb' hap ?_ ?_
        · intro e
          have := congrArg summands e
          rw [summands_ofSummands _ hprin] at this
          simp [summands] at this
        · intro h' rest' hs'
          rw [summands_ofSummands _ hprin, List.cons.injEq] at hs'
          obtain ⟨e2, -⟩ := hs'
          subst e2
          exact ht.plus_head (h' := y) (rest := l'' ++ rest) (by rw [hst]; rfl)
  | zero =>
    intro l rest _ hst
    cases l with
    | nil => exact WNF.zero
    | cons _ _ => simp [summands] at hst
  | _ =>
    intro l rest ht hst
    cases l with
    | nil => exact WNF.zero
    | cons x l' =>
      simp only [summands, List.cons_append, List.cons.injEq] at hst
      obtain ⟨e1, hst⟩ := hst; subst e1; cases l' with
        | nil => exact ht
        | cons _ _ => simp at hst

theorem predT_WNF {c : Tm} (hc : WNF c) (hs : isSucc c = true) : WNF (predT c) := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  rw [predT_of_summands hys]
  exact WNF_ofSummands_prefix c ys [one] hc hys

end MahloOCF
