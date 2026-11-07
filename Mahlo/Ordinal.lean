
/-! Ordinals as well-order classes: order, suprema, Hartogs, arithmetic and principal ordinals.

Copied unchanged from the Compact repository (`Compact/OCFRathjen/Ordinal.lean`), itself copied from Subsp. -/

namespace OCF

universe u

structure WellOrder where
  Carrier : Type u
  lt : Carrier → Carrier → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace WellOrder

structure Iso (A B : WellOrder.{u}) where
  toFun : A.Carrier → B.Carrier
  invFun : B.Carrier → A.Carrier
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  lt_iff : ∀ a b, B.lt (toFun a) (toFun b) ↔ A.lt a b

def Iso.refl (A : WellOrder.{u}) : Iso A A where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

def Iso.trans {A B C : WellOrder.{u}} (e : Iso A B) (f : Iso B C) : Iso A C where
  toFun a := f.toFun (e.toFun a)
  invFun c := e.invFun (f.invFun c)
  left_inv a := by
    rw [f.left_inv, e.left_inv]
  right_inv c := by
    rw [e.right_inv, f.right_inv]
  lt_iff a b := Iff.trans (f.lt_iff (e.toFun a) (e.toFun b)) (e.lt_iff a b)

def Iso.symm {A B : WellOrder.{u}} (e : Iso A B) : Iso B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  lt_iff a b := by
    have h := e.lt_iff (e.invFun a) (e.invFun b)
    rw [e.right_inv a, e.right_inv b] at h
    exact h.symm

def below (A : WellOrder.{u}) (a : A.Carrier) : WellOrder.{u} where
  Carrier := { b : A.Carrier // A.lt b a }
  lt b c := A.lt b.1 c.1
  irrefl b := A.irrefl b.1
  trans b c d hbc hcd := A.trans b.1 c.1 d.1 hbc hcd
  total b c := by
    cases A.total b.1 c.1 with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (Subtype.ext h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf Subtype.val A.wellFounded

def Iso.below {A B : WellOrder.{u}} (e : Iso A B) (a : A.Carrier) :
    Iso (A.below a) (B.below (e.toFun a)) where
  toFun b := ⟨e.toFun b.1, (e.lt_iff b.1 a).mpr b.2⟩
  invFun b := ⟨e.invFun b.1, by
    apply (e.lt_iff (e.invFun b.1) a).mp
    rw [e.right_inv b.1]
    exact b.2⟩
  left_inv b := Subtype.ext (e.left_inv b.1)
  right_inv b := Subtype.ext (e.right_inv b.1)
  lt_iff b c := e.lt_iff b.1 c.1

def belowBelowIso (A : WellOrder.{u}) (a : A.Carrier) (b : (A.below a).Carrier) :
    Iso ((A.below a).below b) (A.below b.1) where
  toFun c := ⟨c.1.1, c.2⟩
  invFun c := ⟨⟨c.1, A.trans c.1 b.1 a c.2 b.2⟩, c.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

def Below (A B : WellOrder.{u}) : Prop :=
  ∃ b : B.Carrier, Nonempty (Iso A (B.below b))

theorem Below.iso_right {A B C : WellOrder.{u}} (e : Iso B C) (h : Below A B) :
    Below A C := by
  cases h with
  | intro b hb =>
    cases hb with
    | intro f =>
      exact Exists.intro (e.toFun b) (Nonempty.intro (f.trans (e.below b)))

theorem Below.iso_left {A B C : WellOrder.{u}} (e : Iso A B) (h : Below B C) :
    Below A C := by
  cases h with
  | intro c hc =>
    cases hc with
    | intro f => exact Exists.intro c (Nonempty.intro (e.trans f))

theorem acc_of_iso {A B : WellOrder.{u}} (e : Iso A B) (h : Acc Below B) :
    Acc Below A := by
  induction h generalizing A with
  | intro B _ ih =>
    apply Acc.intro
    intro C hC
    exact ih C (Below.iso_right e hC) (Iso.refl C)

theorem below_acc (A : WellOrder.{u}) (a : A.Carrier) : Acc Below (A.below a) := by
  induction a using A.wellFounded.induction with
  | h a ih =>
    apply Acc.intro
    intro B hB
    cases hB with
    | intro b hb =>
      cases hb with
      | intro e =>
        exact acc_of_iso (e.trans (belowBelowIso A a b)) (ih b.1 b.2)

theorem below_wellFounded : WellFounded Below.{u} := by
  apply WellFounded.intro
  intro A
  apply Acc.intro
  intro B hB
  cases hB with
  | intro a ha =>
    cases ha with
    | intro e => exact acc_of_iso e (below_acc A a)

theorem Below.irrefl (A : WellOrder.{u}) : ¬ Below A A := by
  have h := below_wellFounded.apply A
  induction h with
  | intro A _ ih =>
    intro hAA
    exact ih A hAA hAA

theorem Below.trans {A B C : WellOrder.{u}} (hAB : Below A B) (hBC : Below B C) :
    Below A C := by
  cases hBC with
  | intro c hc =>
    cases hc with
    | intro e =>
      cases Below.iso_right e hAB with
      | intro b hb =>
        cases hb with
        | intro f =>
          exact Exists.intro b.1 (Nonempty.intro (f.trans (belowBelowIso C c b)))

theorem Below.congr {A B C D : WellOrder.{u}} (e : Iso A B) (f : Iso C D) :
    Below A C ↔ Below B D := by
  apply Iff.intro
  · intro h
    exact Below.iso_right f (Below.iso_left e.symm h)
  · intro h
    exact Below.iso_right f.symm (Below.iso_left e h)

theorem not_below_of_iso {A B : WellOrder.{u}} (e : Iso A B) : ¬ Below A B := by
  intro h
  exact Below.irrefl A (Below.iso_right e.symm h)

theorem below_self (A : WellOrder.{u}) (a : A.Carrier) : Below (A.below a) A :=
  Exists.intro a (Nonempty.intro (Iso.refl (A.below a)))

theorem below_below_of_lt (A : WellOrder.{u}) (a b : A.Carrier) (h : A.lt a b) :
    Below (A.below a) (A.below b) :=
  Exists.intro ⟨a, h⟩ (Nonempty.intro (belowBelowIso A b ⟨a, h⟩).symm)

theorem lt_of_below_below (A : WellOrder.{u}) (a b : A.Carrier)
    (h : Below (A.below a) (A.below b)) : A.lt a b := by
  cases A.total a b with
  | inl hab => exact hab
  | inr hrest =>
    cases hrest with
    | inl hab =>
      cases hab
      exact False.elim (Below.irrefl (A.below a) h)
    | inr hba =>
      exact False.elim
        (Below.irrefl (A.below a) (Below.trans h (below_below_of_lt A b a hba)))

theorem eq_of_below_iso (A : WellOrder.{u}) (a b : A.Carrier)
    (e : Iso (A.below a) (A.below b)) : a = b := by
  cases A.total a b with
  | inl hab => exact False.elim (not_below_of_iso e (below_below_of_lt A a b hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba =>
      exact False.elim (not_below_of_iso e.symm (below_below_of_lt A b a hba))

theorem exists_min (A : WellOrder.{u}) (P : A.Carrier → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, A.lt b a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, A.lt b c → ¬ P b := by
    intro a
    induction a using A.wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, A.lt b a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

def Matches (A B : WellOrder.{u}) (a : A.Carrier) (b : B.Carrier) : Prop :=
  Nonempty (Iso (A.below a) (B.below b))

theorem Matches.unique_left {A B : WellOrder.{u}} {a c : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c b) : a = c := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso A a c (e.trans f.symm)

theorem Matches.unique_right {A B : WellOrder.{u}} {a : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B a d) : b = d := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso B b d (e.symm.trans f)

theorem Matches.lt_iff {A B : WellOrder.{u}} {a c : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c d) : B.lt b d ↔ A.lt a c := by
  cases h with
  | intro e =>
    cases k with
    | intro f =>
      apply Iff.intro
      · intro hbd
        exact lt_of_below_below A a c
          ((Below.congr e f).mpr (below_below_of_lt B b d hbd))
      · intro hac
        exact lt_of_below_below B b d
          ((Below.congr e f).mp (below_below_of_lt A a c hac))

theorem Matches.down {A B : WellOrder.{u}} {a : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (d : B.Carrier) (hdb : B.lt d b) :
    ∃ c, A.lt c a ∧ Matches A B c d := by
  cases h with
  | intro e =>
    let c := e.invFun ⟨d, hdb⟩
    have f := ((belowBelowIso A a c).symm.trans (e.below c)).trans
      (belowBelowIso B b (e.toFun c))
    have he : (e.toFun c).1 = d := congrArg Subtype.val (e.right_inv ⟨d, hdb⟩)
    rw [he] at f
    exact Exists.intro c.1 (And.intro c.2 (Nonempty.intro f))

theorem Matches.below_right {A B : WellOrder.{u}} (b : B.Carrier)
    (a : A.Carrier) (c : (B.below b).Carrier) :
    Matches A (B.below b) a c ↔ Matches A B a c.1 := by
  apply Iff.intro
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c))
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c).symm)

theorem iso_of_matches {A B : WellOrder.{u}}
    (hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b)
    (hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b) : Nonempty (Iso A B) := by
  classical
  let f : A.Carrier → B.Carrier := fun a => Classical.choose (hA a)
  let g : B.Carrier → A.Carrier := fun b => Classical.choose (hB b)
  have hf : ∀ a, Matches A B a (f a) := fun a => Classical.choose_spec (hA a)
  have hg : ∀ b, Matches A B (g b) b := fun b => Classical.choose_spec (hB b)
  exact Nonempty.intro {
    toFun := f
    invFun := g
    left_inv := fun a => Matches.unique_left (hg (f a)) (hf a)
    right_inv := fun b => Matches.unique_right (hf (g b)) (hg b)
    lt_iff := fun a c => Matches.lt_iff (hf a) (hf c)
  }

theorem compare (A B : WellOrder.{u}) : Below A B ∨ Nonempty (Iso A B) ∨ Below B A := by
  classical
  induction A using below_wellFounded.induction generalizing B with
  | h A ih =>
    by_cases hBA : Below B A
    · exact Or.inr (Or.inr hBA)
    · have hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b := by
        intro a
        cases ih (A.below a) (below_self A a) B with
        | inl h => exact h
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro e => exact False.elim (hBA (Exists.intro a (Nonempty.intro e.symm)))
          | inr h => exact False.elim (hBA (Below.trans h (below_self A a)))
      by_cases hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b
      · exact Or.inr (Or.inl (iso_of_matches hA hB))
      · have hmissing : ∃ b : B.Carrier, ¬ ∃ a : A.Carrier, Matches A B a b :=
          Classical.not_forall.mp hB
        cases B.exists_min (fun b => ¬ ∃ a, Matches A B a b) hmissing with
        | intro b hb =>
          have hAc : ∀ a : A.Carrier, ∃ c : (B.below b).Carrier,
              Matches A (B.below b) a c := by
            intro a
            cases hA a with
            | intro c hc =>
              have hcb : B.lt c b := by
                cases B.total c b with
                | inl h => exact h
                | inr h =>
                  cases h with
                  | inl h =>
                    cases h
                    exact False.elim (hb.1 (Exists.intro a hc))
                  | inr h =>
                    cases Matches.down hc b h with
                    | intro d hd => exact False.elim (hb.1 (Exists.intro d hd.2))
              exact Exists.intro ⟨c, hcb⟩ ((Matches.below_right b a ⟨c, hcb⟩).mpr hc)
          have hBc : ∀ c : (B.below b).Carrier, ∃ a : A.Carrier,
              Matches A (B.below b) a c := by
            intro c
            have hc : ∃ a : A.Carrier, Matches A B a c.1 :=
              Classical.byContradiction (fun h => hb.2 c.1 c.2 h)
            cases hc with
            | intro a ha =>
              exact Exists.intro a ((Matches.below_right b a c).mpr ha)
          exact Or.inl (Exists.intro b (iso_of_matches hAc hBc))

end WellOrder

def WellOrder.isoSetoid : Setoid WellOrder.{u} where
  r A B := Nonempty (WellOrder.Iso A B)
  iseqv := {
    refl := fun A => Nonempty.intro (WellOrder.Iso.refl A)
    symm := fun h => by
      cases h with
      | intro e => exact Nonempty.intro e.symm
    trans := fun hAB hBC => by
      cases hAB with
      | intro e =>
        cases hBC with
        | intro f => exact Nonempty.intro (e.trans f)
  }

def Ordinal : Type (u + 1) := Quotient WellOrder.isoSetoid.{u}

namespace Ordinal

def type (A : WellOrder.{u}) : Ordinal.{u} := Quotient.mk WellOrder.isoSetoid A

def lt (a b : Ordinal.{u}) : Prop :=
  Quotient.liftOn₂ a b WellOrder.Below (by
    intro A B C D hAC hBD
    cases hAC with
    | intro e =>
      cases hBD with
      | intro f => exact propext (WellOrder.Below.congr e f))

instance : LT Ordinal.{u} where
  lt := lt

theorem type_eq_of_iso {A B : WellOrder.{u}} (e : WellOrder.Iso A B) :
    type A = type B := Quotient.sound (Nonempty.intro e)

theorem iso_of_type_eq {A B : WellOrder.{u}} (h : type A = type B) :
    Nonempty (WellOrder.Iso A B) := Quotient.exact h

theorem type_acc (A : WellOrder.{u}) : Acc (fun a b : Ordinal.{u} => a < b) (type A) := by
  have hA := WellOrder.below_wellFounded.apply A
  induction hA with
  | intro A _ ih =>
    apply Acc.intro
    intro b
    refine Quotient.inductionOn b ?_
    intro B hBA
    exact ih B hBA

theorem lt_wellFounded : WellFounded (fun a b : Ordinal.{u} => a < b) := by
  apply WellFounded.intro
  intro a
  refine Quotient.inductionOn a ?_
  intro A
  exact type_acc A

theorem lt_irrefl (a : Ordinal.{u}) : ¬ a < a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact WellOrder.Below.irrefl A

theorem lt_trans (a b c : Ordinal.{u}) : a < b → b < c → a < c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C hAB hBC
  exact WellOrder.Below.trans hAB hBC

theorem lt_asymm {a b : Ordinal.{u}} (hab : a < b) : ¬ b < a := by
  intro hba
  exact lt_irrefl a (lt_trans a b a hab hba)

theorem lt_total (a b : Ordinal.{u}) : a < b ∨ a = b ∨ b < a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  cases WellOrder.compare A B with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro e => exact Or.inr (Or.inl (type_eq_of_iso e))
    | inr h => exact Or.inr (Or.inr h)

instance : LE Ordinal.{u} where
  le a b := a < b ∨ a = b

theorem le_refl (a : Ordinal.{u}) : a ≤ a := Or.inr rfl

theorem le_trans {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab =>
    cases hbc with
    | inl hbc => exact Or.inl (lt_trans a b c hab hbc)
    | inr hbc =>
      cases hbc
      exact Or.inl hab
  | inr hab =>
    cases hab
    exact hbc

theorem le_antisymm {a b : Ordinal.{u}} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | inl hab =>
    cases hba with
    | inl hba => exact False.elim (lt_asymm hab hba)
    | inr hba => exact hba.symm
  | inr hab => exact hab

theorem not_lt_iff_le (a b : Ordinal.{u}) : (¬ a < b) ↔ b ≤ a := by
  apply Iff.intro
  · intro h
    cases lt_total a b with
    | inl hab => exact False.elim (h hab)
    | inr hrest =>
      cases hrest with
      | inl hab => exact Or.inr hab.symm
      | inr hba => exact Or.inl hba
  · intro h hab
    cases h with
    | inl hba => exact lt_asymm hab hba
    | inr hba =>
      cases hba
      exact lt_irrefl a hab

theorem lt_type_iff (a : Ordinal.{u}) (B : WellOrder.{u}) :
    a < type B ↔ ∃ b : B.Carrier, a = type (B.below b) := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Iff.intro
  · intro h
    cases h with
    | intro b hb =>
      cases hb with
      | intro e => exact Exists.intro b (type_eq_of_iso e)
  · intro h
    cases h with
    | intro b hb => exact Exists.intro b (iso_of_type_eq hb)

theorem representative_exists (a : Ordinal.{u}) : ∃ A : WellOrder.{u}, type A = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Exists.intro A rfl

noncomputable def representative (a : Ordinal.{u}) : WellOrder.{u} :=
  Classical.choose (representative_exists a)

theorem type_representative (a : Ordinal.{u}) : type (representative a) = a :=
  Classical.choose_spec (representative_exists a)

/-- 同じ順序数を表す整列集合は順序同型である。 -/
theorem type_eq_iff_iso {A B : WellOrder.{u}} :
    type A = type B ↔ Nonempty (WellOrder.Iso A B) := by
  apply Iff.intro
  · exact iso_of_type_eq
  · intro h
    cases h with
    | intro e => exact type_eq_of_iso e

/-- Equality of order types gives a concrete order isomorphism, including its
inverse and the equivalence of the two strict orders. -/
noncomputable def orderIsoOfTypeEq {A B : WellOrder.{u}} (h : type A = type B) :
    WellOrder.Iso A B :=
  Classical.choice (type_eq_iff_iso.mp h)

/-- A concrete order isomorphism between a well-order and the chosen
representative of its order type. -/
noncomputable def representativeOrderIso {a : Ordinal.{u}} (A : WellOrder.{u})
    (hA : type A = a) : WellOrder.Iso A (representative a) :=
  orderIsoOfTypeEq (hA.trans (type_representative a).symm)

theorem initial_lt (a : Ordinal.{u}) (x : (representative a).Carrier) :
    type ((representative a).below x) < a := by
  have h : type ((representative a).below x) < type (representative a) :=
    WellOrder.below_self (representative a) x
  rw [type_representative a] at h
  exact h

theorem initial_injective (a : Ordinal.{u}) (x y : (representative a).Carrier)
    (h : type ((representative a).below x) = type ((representative a).below y)) : x = y := by
  cases iso_of_type_eq h with
  | intro e => exact WellOrder.eq_of_below_iso (representative a) x y e

theorem initial_surjective (a b : Ordinal.{u}) (h : b < a) :
    ∃ x : (representative a).Carrier, b = type ((representative a).below x) := by
  apply (lt_type_iff b (representative a)).mp
  rw [type_representative a]
  exact h

/-- Any ordinal below the type of a well-order injects into its carrier. -/
theorem injective_of_lt_type {a : Ordinal.{u}} (A : WellOrder.{u}) (h : a < type A) :
    ∃ f : (representative a).Carrier → A.Carrier, ∀ x y, f x = f y → x = y := by
  classical
  let f : (representative a).Carrier → A.Carrier := fun x =>
    Classical.choose ((lt_type_iff (type ((representative a).below x)) A).mp
      (lt_trans _ a (type A) (initial_lt a x) h))
  have hf : ∀ x, type ((representative a).below x) = type (A.below (f x)) := by
    intro x
    exact Classical.choose_spec ((lt_type_iff (type ((representative a).below x)) A).mp
      (lt_trans _ a (type A) (initial_lt a x) h))
  refine ⟨f, ?_⟩
  intro x y hxy
  apply initial_injective a x y
  exact (hf x).trans ((congrArg (fun z => type (A.below z)) hxy).trans (hf y).symm)

/-- If `a` is at most the type of a well-order, its representative injects into the carrier. -/
theorem injective_of_le_type {a : Ordinal.{u}} (A : WellOrder.{u}) (h : a ≤ type A) :
    ∃ f : (representative a).Carrier → A.Carrier, ∀ x y, f x = f y → x = y := by
  cases h with
  | inl hlt => exact injective_of_lt_type A hlt
  | inr heq =>
    have htypes : type (representative a) = type A := (type_representative a).trans heq
    cases iso_of_type_eq htypes with
    | intro e =>
      refine ⟨e.toFun, ?_⟩
      intro x y hxy
      have h' := congrArg e.invFun hxy
      rw [e.left_inv x, e.left_inv y] at h'
      exact h'

theorem exists_min (P : Ordinal.{u} → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, b < a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, b < c → ¬ P b := by
    intro a
    induction a using lt_wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, b < a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

theorem initial_lt_iff (a : Ordinal.{u}) (x y : (representative a).Carrier) :
    type ((representative a).below x) < type ((representative a).below y) ↔
      (representative a).lt x y := by
  apply Iff.intro
  · intro h
    exact WellOrder.lt_of_below_below (representative a) x y h
  · intro h
    exact WellOrder.below_below_of_lt (representative a) x y h

def orderOn {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y) : WellOrder.{u} where
  Carrier := X
  lt x y := f x < f y
  irrefl x := lt_irrefl (f x)
  trans x y z hxy hyz := lt_trans (f x) (f y) (f z) hxy hyz
  total x y := by
    cases lt_total (f x) (f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (hf x y h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf f lt_wellFounded

noncomputable def orderOnBelowIso {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    WellOrder.Iso ((orderOn f hf).below x) (representative (f x)) := by
  let F : ((orderOn f hf).below x).Carrier → (representative (f x)).Carrier :=
    fun y => Classical.choose (initial_surjective (f x) (f y.1) y.2)
  have hF : ∀ y, f y.1 = type ((representative (f x)).below (F y)) :=
    fun y => Classical.choose_spec (initial_surjective (f x) (f y.1) y.2)
  let G : (representative (f x)).Carrier → ((orderOn f hf).below x).Carrier :=
    fun b =>
      let y := Classical.choose (hd x _ (initial_lt (f x) b))
      have hy : f y = type ((representative (f x)).below b) :=
        Classical.choose_spec (hd x _ (initial_lt (f x) b))
      ⟨y, by
        change f y < f x
        rw [hy]
        exact initial_lt (f x) b⟩
  have hG : ∀ b, f (G b).1 = type ((representative (f x)).below b) :=
    fun b => Classical.choose_spec (hd x _ (initial_lt (f x) b))
  exact {
    toFun := F
    invFun := G
    left_inv := fun y => Subtype.ext (hf _ _ ((hG (F y)).trans (hF y).symm))
    right_inv := fun b => initial_injective (f x) _ _ ((hF (G b)).symm.trans (hG b))
    lt_iff := fun y z => by
      have h := initial_lt_iff (f x) (F y) (F z)
      rw [← hF y, ← hF z] at h
      exact h.symm
  }

theorem type_orderOn_below {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    type ((orderOn f hf).below x) = f x :=
  (type_eq_of_iso (orderOnBelowIso f hf hd x)).trans (type_representative (f x))

theorem lt_type_orderOn_iff {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (a : Ordinal.{u}) :
    a < type (orderOn f hf) ↔ ∃ x, a = f x := by
  apply Iff.intro
  · intro h
    cases (lt_type_iff a (orderOn f hf)).mp h with
    | intro x hx => exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x))
  · intro h
    cases h with
    | intro x hx =>
      apply (lt_type_iff a (orderOn f hf)).mpr
      exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x).symm)

def SupPoint {I : Type u} (f : I → Ordinal.{u}) :=
  (i : I) × (representative (f i)).Carrier

noncomputable def supPointValue {I : Type u} (f : I → Ordinal.{u}) (p : SupPoint f) :
    Ordinal.{u} := type ((representative (f p.1)).below p.2)

def supSetoid {I : Type u} (f : I → Ordinal.{u}) : Setoid (SupPoint f) where
  r p q := supPointValue f p = supPointValue f q
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h k => h.trans k
  }

def SupCarrier {I : Type u} (f : I → Ordinal.{u}) := Quotient (supSetoid f)

noncomputable def supValue {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f) :
    Ordinal.{u} := Quotient.liftOn x (supPointValue f) (fun _ _ h => h)

theorem supValue_injective {I : Type u} (f : I → Ordinal.{u}) (x y : SupCarrier f) :
    supValue f x = supValue f y → x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact Quotient.sound h

theorem supValue_downward {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f)
    (a : Ordinal.{u}) : a < supValue f x → ∃ y, supValue f y = a := by
  refine Quotient.inductionOn x ?_
  intro p h
  have ha : a < f p.1 := lt_trans a _ (f p.1) h (initial_lt (f p.1) p.2)
  cases initial_surjective (f p.1) a ha with
  | intro b hb =>
    exact Exists.intro (Quotient.mk (supSetoid f) ⟨p.1, b⟩) hb.symm

noncomputable def sup {I : Type u} (f : I → Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (supValue f) (supValue_injective f))

theorem lt_sup_iff {I : Type u} (f : I → Ordinal.{u}) (a : Ordinal.{u}) :
    a < sup f ↔ ∃ i, a < f i := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (supValue f) (supValue_injective f)
        (supValue_downward f) a).mp h with
    | intro x hx =>
      revert hx
      refine Quotient.inductionOn x ?_
      intro p hp
      rw [hp]
      exact Exists.intro p.1 (initial_lt (f p.1) p.2)
  · intro h
    cases h with
    | intro i hi =>
      cases initial_surjective (f i) a hi with
      | intro b hb =>
        apply (lt_type_orderOn_iff (supValue f) (supValue_injective f)
          (supValue_downward f) a).mpr
        exact Exists.intro (Quotient.mk (supSetoid f) ⟨i, b⟩) hb

theorem le_sup {I : Type u} (f : I → Ordinal.{u}) (i : I) : f i ≤ sup f := by
  apply (not_lt_iff_le (sup f) (f i)).mp
  intro h
  exact lt_irrefl (sup f) ((lt_sup_iff f (sup f)).mpr (Exists.intro i h))

theorem sup_le_iff {I : Type u} (f : I → Ordinal.{u}) (b : Ordinal.{u}) :
    sup f ≤ b ↔ ∀ i, f i ≤ b := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_sup f i) h
  · intro h
    apply (not_lt_iff_le b (sup f)).mp
    intro hb
    cases (lt_sup_iff f b).mp hb with
    | intro i hi => exact ((not_lt_iff_le b (f i)).mpr (h i)) hi

theorem sup_mono {I : Type u} (f g : I → Ordinal.{u}) (h : ∀ i, f i ≤ g i) :
    sup f ≤ sup g := by
  apply (sup_le_iff f (sup g)).mpr
  intro i
  exact le_trans (h i) (le_sup g i)

noncomputable def zero : Ordinal.{u} := sup (fun x : PEmpty.{u+1} => nomatch x)

noncomputable instance : OfNat Ordinal.{u} 0 where
  ofNat := zero

theorem not_lt_zero (a : Ordinal.{u}) : ¬ a < 0 := by
  intro h
  cases (lt_sup_iff (fun x : PEmpty.{u+1} => nomatch x) a).mp h with
  | intro x _ => exact PEmpty.elim x

theorem zero_le (a : Ordinal.{u}) : 0 ≤ a :=
  (not_lt_iff_le a 0).mp (not_lt_zero a)

theorem zero_lt_iff_ne_zero (a : Ordinal.{u}) : 0 < a ↔ a ≠ 0 := by
  apply Iff.intro
  · intro h heq
    cases heq
    exact lt_irrefl 0 h
  · intro h
    cases zero_le a with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (h heq.symm)

noncomputable def succValue (a : Ordinal.{u}) : Option (representative a).Carrier → Ordinal.{u}
  | none => a
  | some x => type ((representative a).below x)

theorem succValue_injective (a : Ordinal.{u}) (x y : Option (representative a).Carrier) :
    succValue a x = succValue a y → x = y := by
  cases x with
  | none =>
    cases y with
    | none => intro _; rfl
    | some y =>
      intro h
      have hy := initial_lt a y
      change a = type ((representative a).below y) at h
      rw [← h] at hy
      exact False.elim (lt_irrefl a hy)
  | some x =>
    cases y with
    | none =>
      intro h
      have hx := initial_lt a x
      change type ((representative a).below x) = a at h
      rw [h] at hx
      exact False.elim (lt_irrefl a hx)
    | some y =>
      intro h
      exact congrArg Option.some (initial_injective a x y h)

theorem succValue_downward (a : Ordinal.{u}) (x : Option (representative a).Carrier)
    (b : Ordinal.{u}) (h : b < succValue a x) : ∃ y, succValue a y = b := by
  have hba : b < a := by
    cases x with
    | none => exact h
    | some x => exact lt_trans b _ a h (initial_lt a x)
  cases initial_surjective a b hba with
  | intro y hy => exact Exists.intro (some y) hy.symm

noncomputable def succ (a : Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (succValue a) (succValue_injective a))

theorem lt_succ_iff_le (a b : Ordinal.{u}) : a < succ b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (succValue b) (succValue_injective b)
        (succValue_downward b) a).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inr hx
      | some x =>
        rw [hx]
        exact Or.inl (initial_lt b x)
  · intro h
    apply (lt_type_orderOn_iff (succValue b) (succValue_injective b)
      (succValue_downward b) a).mpr
    cases h with
    | inl h =>
      cases initial_surjective b a h with
      | intro x hx => exact Exists.intro (some x) hx
    | inr h => exact Exists.intro none h

theorem lt_succ_self (a : Ordinal.{u}) : a < succ a :=
  (lt_succ_iff_le a a).mpr (le_refl a)

theorem lt_of_le_of_lt {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b < c) : a < c := by
  cases hab with
  | inl hab => exact lt_trans a b c hab hbc
  | inr hab =>
    cases hab
    exact hbc

theorem lt_of_lt_of_le {a b c : Ordinal.{u}} (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hbc => exact lt_trans a b c hab hbc
  | inr hbc =>
    cases hbc
    exact hab

theorem succ_le_iff_lt (a b : Ordinal.{u}) : succ a ≤ b ↔ a < b := by
  apply Iff.intro
  · intro h
    exact lt_of_lt_of_le (lt_succ_self a) h
  · intro h
    apply (not_lt_iff_le b (succ a)).mp
    intro hb
    have hba := (lt_succ_iff_le b a).mp hb
    exact lt_irrefl b (lt_of_le_of_lt hba h)

theorem succ_mono {a b : Ordinal.{u}} (h : a ≤ b) : succ a ≤ succ b :=
  (succ_le_iff_lt a (succ b)).mpr ((lt_succ_iff_le a b).mpr h)

end Ordinal

structure SubOrder (X : Type u) where
  domain : X → Prop
  lt : {x : X // domain x} → {x : X // domain x} → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace SubOrder

def toWellOrder {X : Type u} (r : SubOrder X) : WellOrder.{u} where
  Carrier := {x : X // r.domain x}
  lt := r.lt
  irrefl := r.irrefl
  trans := r.trans
  total := r.total
  wellFounded := r.wellFounded

noncomputable def preimage {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) : A :=
  Classical.choose x.2

theorem preimage_spec {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) :
    f (preimage f x) = x.1 := Classical.choose_spec x.2

theorem preimage_image {A X : Type u} (f : A → X)
    (hf : ∀ a b, f a = f b → a = b) (a : A) :
    preimage f ⟨f a, Exists.intro a rfl⟩ = a :=
  hf _ a (preimage_spec f ⟨f a, Exists.intro a rfl⟩)

noncomputable def image {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (_hf : ∀ a b, f a = f b → a = b) : SubOrder X where
  domain x := ∃ a, f a = x
  lt x y := A.lt (preimage f x) (preimage f y)
  irrefl x := A.irrefl (preimage f x)
  trans x y z hxy hyz := A.trans _ _ _ hxy hyz
  total x y := by
    cases A.total (preimage f x) (preimage f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h =>
        apply Or.inr
        apply Or.inl
        apply Subtype.ext
        exact (preimage_spec f x).symm.trans ((congrArg f h).trans (preimage_spec f y))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf (preimage f) A.wellFounded

noncomputable def imageIso {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (hf : ∀ a b, f a = f b → a = b) : WellOrder.Iso A (image A f hf).toWellOrder where
  toFun a := ⟨f a, Exists.intro a rfl⟩
  invFun := preimage f
  left_inv a := preimage_image f hf a
  right_inv x := Subtype.ext (preimage_spec f x)
  lt_iff a b := by
    change A.lt (preimage f ⟨f a, Exists.intro a rfl⟩)
      (preimage f ⟨f b, Exists.intro b rfl⟩) ↔ A.lt a b
    rw [preimage_image f hf a, preimage_image f hf b]

theorem type_image_eq {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (hf : ∀ a b, f a = f b → a = b) :
    Ordinal.type (image A f hf).toWellOrder = Ordinal.type A :=
  Ordinal.type_eq_of_iso (imageIso A f hf).symm

end SubOrder

namespace Ordinal

noncomputable def hartogs (X : Type u) : Ordinal.{u} :=
  sup (fun r : SubOrder X => succ (type r.toWellOrder))

theorem subOrder_type_lt_hartogs {X : Type u} (r : SubOrder X) :
    type r.toWellOrder < hartogs X :=
  lt_of_lt_of_le (lt_succ_self (type r.toWellOrder))
    (le_sup (fun s : SubOrder X => succ (type s.toWellOrder)) r)

theorem lt_hartogs_of_injective {X : Type u} (a : Ordinal.{u})
    (f : (representative a).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    a < hartogs X := by
  have he := type_eq_of_iso (SubOrder.imageIso (representative a) f hf)
  have h := subOrder_type_lt_hartogs (SubOrder.image (representative a) f hf)
  rw [← he, type_representative a] at h
  exact h

/-- Every ordinal below the Hartogs ordinal injects into the underlying type. -/
theorem injective_of_lt_hartogs {X : Type u} {a : Ordinal.{u}} (h : a < hartogs X) :
    ∃ f : (representative a).Carrier → X, ∀ x y, f x = f y → x = y := by
  unfold hartogs at h
  cases (lt_sup_iff (fun r : SubOrder X => succ (type r.toWellOrder)) a).mp h with
  | intro r hr =>
    cases injective_of_le_type r.toWellOrder ((lt_succ_iff_le a (type r.toWellOrder)).mp hr) with
    | intro f hf =>
      exact ⟨fun x => (f x).1, fun x y hxy => hf x y (Subtype.ext hxy)⟩

/-- The Hartogs ordinal is exactly the first ordinal that does not inject into `X`. -/
theorem lt_hartogs_iff_injective (X : Type u) (a : Ordinal.{u}) :
    a < hartogs X ↔ ∃ f : (representative a).Carrier → X, ∀ x y, f x = f y → x = y := by
  apply Iff.intro
  · exact injective_of_lt_hartogs
  · intro h
    cases h with
    | intro f hf => exact lt_hartogs_of_injective a f hf

theorem no_injection_hartogs (X : Type u) (f : (representative (hartogs X)).Carrier → X) :
    ¬ (∀ x y, f x = f y → x = y) := by
  intro hf
  exact lt_irrefl (hartogs X) (lt_hartogs_of_injective (hartogs X) f hf)

theorem eq_of_lt_iff (a b : Ordinal.{u}) (h : ∀ c, c < a ↔ c < b) : a = b := by
  cases lt_total a b with
  | inl hab => exact False.elim (lt_irrefl a ((h a).mpr hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba => exact False.elim (lt_irrefl b ((h b).mp hba))

noncomputable def add (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun b ih => sup (fun x : Option (representative b).Carrier =>
    match x with
    | none => a
    | some x => succ (ih (type ((representative b).below x)) (initial_lt b x))))

noncomputable instance : Add Ordinal.{u} where
  add := add

theorem add_eq (a b : Ordinal.{u}) :
    a + b = sup (fun x : Option (representative b).Carrier =>
      match x with
      | none => a
      | some x => succ (a + type ((representative b).below x))) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem lt_add_iff (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c ≤ a + d := by
  rw [add_eq a b]
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ c).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inl hx
      | some x =>
        exact Or.inr (Exists.intro (type ((representative b).below x))
          (And.intro (initial_lt b x) ((lt_succ_iff_le c _).mp hx)))
  · intro h
    apply (lt_sup_iff _ c).mpr
    cases h with
    | inl h => exact Exists.intro none h
    | inr h =>
      cases h with
      | intro d hd =>
        cases initial_surjective b d hd.1 with
        | intro x hx =>
          refine Exists.intro (some x) ?_
          apply (lt_succ_iff_le c _).mpr
          rw [← hx]
          exact hd.2

theorem le_add (a b : Ordinal.{u}) : a ≤ a + b := by
  rw [add_eq a b]
  exact le_sup _ none

theorem add_lt_add_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b < c) :
    a + b < a + c :=
  (lt_add_iff a c (a + b)).mpr (Or.inr (Exists.intro b (And.intro h (le_refl _))))

theorem add_mono_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b ≤ c) :
    a + b ≤ a + c := by
  cases h with
  | inl h => exact Or.inl (add_lt_add_right a h)
  | inr h =>
    cases h
    exact le_refl _

theorem add_zero (a : Ordinal.{u}) : a + 0 = a := by
  apply le_antisymm
  · rw [add_eq a 0]
    apply (sup_le_iff _ a).mpr
    intro x
    cases x with
    | none => exact le_refl a
    | some x => exact False.elim (not_lt_zero _ (initial_lt 0 x))
  · exact le_add a 0

theorem zero_add (b : Ordinal.{u}) : 0 + b = b := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    apply eq_of_lt_iff
    intro c
    apply Iff.intro
    · intro hcb
      cases (lt_add_iff 0 b c).mp hcb with
      | inl hc0 => exact False.elim (not_lt_zero c hc0)
      | inr hcd =>
        cases hcd with
        | intro d hd =>
          have hcd := hd.2
          rw [ih d hd.1] at hcd
          exact lt_of_le_of_lt hcd hd.1
    · intro hcb
      apply (lt_add_iff 0 b c).mpr
      apply Or.inr
      refine Exists.intro c (And.intro hcb ?_)
      rw [ih c hcb]
      exact le_refl c

theorem add_succ (a b : Ordinal.{u}) : a + succ b = succ (a + b) := by
  apply eq_of_lt_iff
  intro c
  apply Iff.intro
  · intro hc
    apply (lt_succ_iff_le c (a + b)).mpr
    cases (lt_add_iff a (succ b) c).mp hc with
    | inl hca => exact Or.inl (lt_of_lt_of_le hca (le_add a b))
    | inr hcd =>
      cases hcd with
      | intro d hd =>
        exact le_trans hd.2 (add_mono_right a ((lt_succ_iff_le d b).mp hd.1))
  · intro hc
    apply (lt_add_iff a (succ b) c).mpr
    exact Or.inr (Exists.intro b
      (And.intro (lt_succ_self b) ((lt_succ_iff_le c (a + b)).mp hc)))

theorem add_mono_left {a b : Ordinal.{u}} (hab : a ≤ b) (c : Ordinal.{u}) :
    a + c ≤ b + c := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    rw [add_eq a c, add_eq b c]
    apply sup_mono
    intro x
    cases x with
    | none => exact hab
    | some x => exact succ_mono (ih _ (initial_lt c x))

theorem right_le_add (a b : Ordinal.{u}) : b ≤ a + b := by
  have h := add_mono_left (zero_le a) b
  rw [zero_add b] at h
  exact h

theorem add_assoc (a b c : Ordinal.{u}) : (a + b) + c = a + (b + c) := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    apply eq_of_lt_iff
    intro x
    apply Iff.intro
    · intro hx
      cases (lt_add_iff (a + b) c x).mp hx with
      | inl hxab => exact lt_of_lt_of_le hxab (add_mono_right a (le_add b c))
      | inr hxd =>
        cases hxd with
        | intro d hd =>
          have hxd := hd.2
          rw [ih d hd.1] at hxd
          exact lt_of_le_of_lt hxd (add_lt_add_right a (add_lt_add_right b hd.1))
    · intro hx
      cases (lt_add_iff a (b + c) x).mp hx with
      | inl hxa => exact lt_of_lt_of_le hxa (le_trans (le_add a b) (le_add (a + b) c))
      | inr hxy =>
        cases hxy with
        | intro y hy =>
          cases (lt_add_iff b c y).mp hy.1 with
          | inl hyb =>
            exact lt_of_le_of_lt hy.2
              (lt_of_lt_of_le (add_lt_add_right a hyb) (le_add (a + b) c))
          | inr hyd =>
            cases hyd with
            | intro d hd =>
              have hxy := le_trans hy.2 (add_mono_right a hd.2)
              rw [← ih d hd.1] at hxy
              exact lt_of_le_of_lt hxy (add_lt_add_right (a + b) hd.1)

theorem add_right_cancel {a b c : Ordinal.{u}} (h : a + b = a + c) : b = c := by
  cases lt_total b c with
  | inl hbc =>
    have hlt := add_lt_add_right a hbc
    rw [h] at hlt
    exact False.elim (lt_irrefl (a + c) hlt)
  | inr hrest =>
    cases hrest with
    | inl hbc => exact hbc
    | inr hcb =>
      have hlt := add_lt_add_right a hcb
      rw [h] at hlt
      exact False.elim (lt_irrefl (a + c) hlt)

theorem lt_add_iff_eq (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c = a + d := by
  apply Iff.intro
  · intro h
    cases (lt_add_iff a b c).mp h with
    | inl hca => exact Or.inl hca
    | inr hd =>
      cases Ordinal.exists_min (fun d => d < b ∧ c ≤ a + d) hd with
      | intro d hdmin =>
        cases hdmin.1.2 with
        | inr hcd => exact Or.inr (Exists.intro d (And.intro hdmin.1.1 hcd))
        | inl hcd =>
          cases (lt_add_iff a d c).mp hcd with
          | inl hca => exact Or.inl hca
          | inr he =>
            cases he with
            | intro e he =>
              exact False.elim
                (hdmin.2 e he.1 (And.intro (lt_trans e d b he.1 hdmin.1.1) he.2))
  · intro h
    apply (lt_add_iff a b c).mpr
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | intro d hd => exact Or.inr (Exists.intro d (And.intro hd.1 (Or.inr hd.2)))

theorem le_add_cases (a b c : Ordinal.{u}) (h : c ≤ a + b) (hca : ¬ c < a) :
    ∃ d, d ≤ b ∧ c = a + d := by
  cases h with
  | inr h => exact Exists.intro b (And.intro (le_refl b) h)
  | inl h =>
    cases (lt_add_iff_eq a b c).mp h with
    | inl h => exact False.elim (hca h)
    | inr h =>
      cases h with
      | intro d hd => exact Exists.intro d (And.intro (Or.inl hd.1) hd.2)

theorem exists_add_of_le (a b : Ordinal.{u}) (h : a ≤ b) : ∃ c, b = a + c := by
  have hb : b < a + succ b := lt_of_lt_of_le (lt_succ_self b) (right_le_add a (succ b))
  cases (lt_add_iff_eq a (succ b) b).mp hb with
  | inl hba => exact False.elim (((not_lt_iff_le b a).mpr h) hba)
  | inr hc =>
    cases hc with
    | intro c hc => exact Exists.intro c hc.2

def AddPrincipal (k : Ordinal.{u}) : Prop :=
  ∀ a b, a < k → b < k → a + b < k

theorem AddPrincipal.absorb {k : Ordinal.{u}} (hk : AddPrincipal k)
    {a : Ordinal.{u}} (ha : a < k) : a + k = k := by
  apply le_antisymm
  · apply (not_lt_iff_le k (a + k)).mp
    intro h
    cases (lt_add_iff a k k).mp h with
    | inl hka => exact lt_asymm ha hka
    | inr hd =>
      cases hd with
      | intro d hd => exact lt_irrefl k (lt_of_le_of_lt hd.2 (hk a d ha hd.1))
  · exact right_le_add a k

theorem succ_zero_principal : AddPrincipal (succ (0 : Ordinal.{u})) := by
  intro a b ha hb
  have ea := le_antisymm ((lt_succ_iff_le a 0).mp ha) (zero_le a)
  have eb := le_antisymm ((lt_succ_iff_le b 0).mp hb) (zero_le b)
  rw [ea, eb, add_zero]
  exact lt_succ_self 0

noncomputable def principalStage (a : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => succ a
  | n + 1 => principalStage a n + principalStage a n

theorem principalStage_pos (a : Ordinal.{u}) (n : Nat) : 0 < principalStage a n := by
  induction n with
  | zero => exact lt_of_le_of_lt (zero_le a) (lt_succ_self a)
  | succ n ih => exact lt_of_lt_of_le ih (le_add (principalStage a n) (principalStage a n))

theorem principalStage_lt_succ (a : Ordinal.{u}) (n : Nat) :
    principalStage a n < principalStage a (n + 1) := by
  have h := add_lt_add_right (principalStage a n) (principalStage_pos a n)
  rw [add_zero] at h
  exact h

theorem principalStage_mono (a : Ordinal.{u}) {n m : Nat} (h : n ≤ m) :
    principalStage a n ≤ principalStage a m := by
  induction h with
  | refl => exact le_refl _
  | @step m h ih => exact le_trans ih (Or.inl (principalStage_lt_succ a m))

noncomputable def principalHull (a : Ordinal.{u}) : Ordinal.{u} :=
  sup (fun n : ULift.{u} Nat => principalStage a n.down)

theorem principalStage_le_hull (a : Ordinal.{u}) (n : Nat) :
    principalStage a n ≤ principalHull a :=
  le_sup (fun k : ULift.{u} Nat => principalStage a k.down) (ULift.up n)

theorem lt_principalHull (a : Ordinal.{u}) : a < principalHull a :=
  lt_of_lt_of_le (lt_succ_self a) (principalStage_le_hull a 0)

theorem principalHull_principal (a : Ordinal.{u}) : AddPrincipal (principalHull a) := by
  intro x y hx hy
  cases (lt_sup_iff _ x).mp hx with
  | intro n hn =>
    cases (lt_sup_iff _ y).mp hy with
    | intro m hm =>
      have hxk := lt_of_lt_of_le hn (principalStage_mono a (Nat.le_max_left n.down m.down))
      have hyk := lt_of_lt_of_le hm (principalStage_mono a (Nat.le_max_right n.down m.down))
      have hxy := lt_of_le_of_lt (add_mono_left (Or.inl hxk) y)
        (add_lt_add_right (principalStage a (max n.down m.down)) hyk)
      exact lt_of_lt_of_le hxy (principalStage_le_hull a (max n.down m.down + 1))

theorem le_of_lt {a b : Ordinal.{u}} (h : a < b) : a ≤ b := Or.inl h

theorem lt_or_le (a b : Ordinal.{u}) : a < b ∨ b ≤ a := by
  cases lt_total a b with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h => exact Or.inr (Or.inr h.symm)
    | inr h => exact Or.inr (Or.inl h)

theorem le_or_lt (a b : Ordinal.{u}) : a ≤ b ∨ b < a := by
  cases lt_or_le b a with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

theorem le_total (a b : Ordinal.{u}) : a ≤ b ∨ b ≤ a := by
  cases lt_or_le a b with
  | inl h => exact Or.inl (Or.inl h)
  | inr h => exact Or.inr h

theorem lt_of_le_of_ne {a b : Ordinal.{u}} (h : a ≤ b) (hne : a ≠ b) : a < b := by
  cases h with
  | inl h => exact h
  | inr h => exact absurd h hne

theorem not_lt_of_le {a b : Ordinal.{u}} (h : a ≤ b) : ¬ b < a :=
  (not_lt_iff_le b a).mpr h

theorem not_le_of_lt {a b : Ordinal.{u}} (h : a < b) : ¬ b ≤ a :=
  fun h' => not_lt_of_le h' h

theorem le_of_not_lt {a b : Ordinal.{u}} (h : ¬ a < b) : b ≤ a := (not_lt_iff_le a b).mp h

theorem lt_of_not_le {a b : Ordinal.{u}} (h : ¬ a ≤ b) : b < a := by
  cases lt_or_le b a with
  | inl h' => exact h'
  | inr h' => exact absurd h' h

theorem ne_of_lt {a b : Ordinal.{u}} (h : a < b) : a ≠ b := by
  intro e
  rw [e] at h
  exact lt_irrefl b h

theorem ne_of_gt {a b : Ordinal.{u}} (h : b < a) : a ≠ b := fun e => ne_of_lt h e.symm

theorem eq_zero_or_pos (a : Ordinal.{u}) : a = 0 ∨ 0 < a := by
  cases zero_le a with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h.symm

theorem le_zero_iff (a : Ordinal.{u}) : a ≤ 0 ↔ a = 0 := by
  apply Iff.intro
  · intro h
    exact le_antisymm h (zero_le a)
  · intro h
    rw [h]
    exact le_refl 0

theorem pos_of_ne_zero {a : Ordinal.{u}} (h : a ≠ 0) : 0 < a := (zero_lt_iff_ne_zero a).mpr h

theorem le_of_lt_succ {a b : Ordinal.{u}} (h : a < succ b) : a ≤ b := (lt_succ_iff_le a b).mp h

theorem lt_succ_of_le {a b : Ordinal.{u}} (h : a ≤ b) : a < succ b := (lt_succ_iff_le a b).mpr h

theorem succ_le_of_lt {a b : Ordinal.{u}} (h : a < b) : succ a ≤ b := (succ_le_iff_lt a b).mpr h

theorem succ_inj {a b : Ordinal.{u}} (h : succ a = succ b) : a = b := by
  apply le_antisymm
  · apply le_of_lt_succ
    rw [← h]
    exact lt_succ_self a
  · apply le_of_lt_succ
    rw [h]
    exact lt_succ_self b

theorem zero_lt_succ (a : Ordinal.{u}) : 0 < succ a := lt_of_le_of_lt (zero_le a) (lt_succ_self a)

theorem succ_ne_zero (a : Ordinal.{u}) : succ a ≠ 0 := ne_of_gt (zero_lt_succ a)

theorem add_one_eq_succ (a : Ordinal.{u}) : a + succ 0 = succ a := by
  rw [add_succ, add_zero]

theorem add_lt_add_iff_right (a : Ordinal.{u}) {b c : Ordinal.{u}} : a + b < a + c ↔ b < c := by
  apply Iff.intro
  · intro h
    cases lt_or_le b c with
    | inl hbc => exact hbc
    | inr hcb => exact absurd h (not_lt_of_le (add_mono_right a hcb))
  · exact add_lt_add_right a

theorem lt_add_of_pos (a : Ordinal.{u}) {b : Ordinal.{u}} (h : 0 < b) : a < a + b := by
  have h' := add_lt_add_right a h
  rw [add_zero] at h'
  exact h'

noncomputable def supLt (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} :=
  sup (fun x : (representative β).Carrier => F (type ((representative β).below x)))

theorem lt_supLt_iff (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    a < supLt β F ↔ ∃ ξ, ξ < β ∧ a < F ξ := by
  unfold supLt
  rw [lt_sup_iff]
  apply Iff.intro
  · intro h
    cases h with
    | intro x hx => exact Exists.intro _ (And.intro (initial_lt β x) hx)
  · intro h
    cases h with
    | intro ξ hξ =>
      cases initial_surjective β ξ hξ.1 with
      | intro x hx =>
        refine Exists.intro x ?_
        rw [← hx]
        exact hξ.2

theorem le_supLt (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) {ξ : Ordinal.{u}}
    (h : ξ < β) : F ξ ≤ supLt β F := by
  apply le_of_not_lt
  intro hlt
  exact lt_irrefl _ ((lt_supLt_iff β F _).mpr (Exists.intro ξ (And.intro h hlt)))

theorem supLt_le_iff (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) (c : Ordinal.{u}) :
    supLt β F ≤ c ↔ ∀ ξ, ξ < β → F ξ ≤ c := by
  apply Iff.intro
  · intro h ξ hξ
    exact le_trans (le_supLt β F hξ) h
  · intro h
    apply le_of_not_lt
    intro hc
    cases (lt_supLt_iff β F c).mp hc with
    | intro ξ hξ => exact not_lt_of_le (h ξ hξ.1) hξ.2

end Ordinal

/-! ## Generic ordinal notions: least elements, `ω`, limits, closures, enumerations, cofinality,
regularity, smallness (`Small κ A`: fewer than `κ` elements) and Cantor normal forms.

Copied from the Subsp repository (`Subsp/OCF/Jaeger/Ordinal.lean`), omitting the parts specific
to Jäger's collapsing functions (`Inaccessible`, `I`, `regPred`, `Λ₀`, the stages of `C` and `Ψ`). -/

namespace Rathjen

open Ordinal

noncomputable section

def least (P : Ordinal.{u} → Prop) : Ordinal.{u} :=
  open Classical in
  if h : ∃ ξ, P ξ then Classical.choose (Ordinal.exists_min P h) else 0

theorem least_spec (P : Ordinal.{u} → Prop) (h : ∃ ξ, P ξ) :
    P (least P) ∧ ∀ ξ, ξ < least P → ¬ P ξ := by
  unfold least
  rw [dite_eq_left h]
  exact Classical.choose_spec (Ordinal.exists_min P h)

theorem least_le (P : Ordinal.{u} → Prop) {ξ : Ordinal.{u}} (h : P ξ) : least P ≤ ξ :=
  (not_lt_iff_le ξ (least P)).mp
    (fun hlt => (least_spec P (Exists.intro ξ h)).2 ξ hlt h)

def ordNat : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => succ (ordNat n)

def omega : Ordinal.{u} := sup (fun n : ULift.{u} Nat => ordNat n.down)

def IsLimit (α : Ordinal.{u}) : Prop := 0 < α ∧ ∀ β, β < α → succ β < α

def IsSupOf (B : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  (∀ β, B β → β ≤ ξ) ∧ ∀ η, η < ξ → ∃ β, B β ∧ η < β

def IsClosed (A : Ordinal.{u} → Prop) : Prop :=
  ∀ B : Ordinal.{u} → Prop, (∀ β, B β → A β) → (∃ β, B β) → ∀ ξ, IsSupOf B ξ → A ξ

def closure (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  ∀ S : Ordinal.{u} → Prop, (∀ β, A β → S β) → IsClosed S → S ξ

def IsLimitPoint (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  0 < ξ ∧ ∀ η, η < ξ → ∃ β, A β ∧ η < β ∧ β < ξ

theorem closure_iff (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) :
    closure A ξ ↔ A ξ ∨ IsLimitPoint A ξ := by
  apply Iff.intro
  · intro h
    apply h (fun ζ => A ζ ∨ IsLimitPoint A ζ) (fun β hβ => Or.inl hβ)
    intro B hB hne ζ hζ
    cases Classical.em (B ζ) with
    | inl hζB => exact hB ζ hζB
    | inr hζB =>
      have hlt : ∀ β, B β → β < ζ := by
        intro β hβ
        cases hζ.1 β hβ with
        | inl h => exact h
        | inr h =>
          rw [h] at hβ
          exact False.elim (hζB hβ)
      apply Or.inr
      apply And.intro
      · cases hne with
        | intro β hβ => exact lt_of_le_of_lt (zero_le β) (hlt β hβ)
      · intro η hη
        cases hζ.2 η hη with
        | intro β hβ =>
          cases hB β hβ.1 with
          | inl hA => exact Exists.intro β (And.intro hA (And.intro hβ.2 (hlt β hβ.1)))
          | inr hβlim =>
            cases hβlim.2 η hβ.2 with
            | intro a ha =>
              exact Exists.intro a
                (And.intro ha.1 (And.intro ha.2.1 (lt_trans a β ζ ha.2.2 (hlt β hβ.1))))
  · intro h S hAS hS
    cases h with
    | inl hA => exact hAS ξ hA
    | inr hlim =>
      apply hS (fun β => A β ∧ β < ξ) (fun β hβ => hAS β hβ.1)
      · cases hlim.2 0 hlim.1 with
        | intro β hβ => exact Exists.intro β (And.intro hβ.1 hβ.2.2)
      · apply And.intro
        · intro β hβ
          exact Or.inl hβ.2
        · intro η hη
          cases hlim.2 η hη with
          | intro β hβ => exact Exists.intro β (And.intro (And.intro hβ.1 hβ.2.2) hβ.2.1)

def enum (X : Ordinal.{u} → Prop) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun α previous =>
    least (fun ξ => X ξ ∧ ∀ β (h : β < α), previous β h < ξ))

theorem enum_eq (X : Ordinal.{u} → Prop) (α : Ordinal.{u}) :
    enum X α = least (fun ξ => X ξ ∧ ∀ β, β < α → enum X β < ξ) :=
  WellFounded.fix_eq lt_wellFounded _ α

theorem enum_spec (X : Ordinal.{u} → Prop) (α : Ordinal.{u})
    (h : ∃ ξ, X ξ ∧ ∀ β, β < α → enum X β < ξ) :
    X (enum X α) ∧ ∀ β, β < α → enum X β < enum X α := by
  rw [enum_eq X α]
  exact (least_spec _ h).1

theorem enum_le {X : Ordinal.{u} → Prop} {α ξ : Ordinal.{u}} (hX : X ξ)
    (h : ∀ β, β < α → enum X β < ξ) : enum X α ≤ ξ := by
  rw [enum_eq X α]
  exact least_le _ (And.intro hX h)

def CofinalFrom (β α : Ordinal.{u}) : Prop :=
  ∃ f : (representative β).Carrier → Ordinal.{u}, (∀ x, f x < α) ∧ sup f = α

def cf (α : Ordinal.{u}) : Ordinal.{u} := least (fun β => CofinalFrom β α)

def IsRegular (α : Ordinal.{u}) : Prop := IsLimit α ∧ cf α = α

/-- A regular ordinal cannot inject into a smaller ordinal.  This records the
initial-ordinal consequence of `cf κ = κ` using the cofinality notion used in
this development. -/
theorem IsRegular.no_injective_to_smaller {κ β : Ordinal.{u}}
    (hκ : IsRegular κ) (hβ : β < κ)
    (f : (representative κ).Carrier → (representative β).Carrier)
    (hf : ∀ x y, f x = f y → x = y) : False := by
  classical
  let g : (representative β).Carrier → Ordinal.{u} := fun y =>
    if hy : ∃ x, f x = y then
      type ((representative κ).below (Classical.choose hy))
    else 0
  have hgf : ∀ x, g (f x) = type ((representative κ).below x) := by
    intro x
    have hx : ∃ y, f y = f x := ⟨x, rfl⟩
    have heq : Classical.choose hx = x := hf _ _ (Classical.choose_spec hx)
    simp [g, hx, heq]
  have hgbound : ∀ y, g y < κ := by
    intro y
    by_cases hy : ∃ x, f x = y
    · simp only [g, dite_eq_left hy]
      exact initial_lt κ (Classical.choose hy)
    · simp [g, hy, hκ.1.1]
  have hsup : sup g ≤ κ := (sup_le_iff g κ).mpr (fun y => Or.inl (hgbound y))
  have hκsup : κ ≤ sup g := by
    apply (not_lt_iff_le (sup g) κ).mp
    intro hsupκ
    let ξ := sup g
    have hξκ : ξ < κ := by simpa [ξ] using hsupκ
    have hsuccκ : succ ξ < κ := hκ.1.2 ξ hξκ
    obtain ⟨x, hx⟩ := initial_surjective κ (succ ξ) hsuccκ
    have hval : g (f x) = succ ξ := by
      rw [hgf x, ← hx]
    have hle : succ ξ ≤ sup g := by
      simpa only [hval] using le_sup g (f x)
    have hle' : succ ξ ≤ ξ := by simpa [ξ] using hle
    exact lt_irrefl ξ (lt_of_lt_of_le (lt_succ_self ξ) hle')
  have hsup_eq : sup g = κ := le_antisymm hsup hκsup
  have hcof : CofinalFrom β κ := ⟨g, hgbound, hsup_eq⟩
  have hcf : cf κ ≤ β := least_le _ hcof
  rw [hκ.2] at hcf
  exact lt_irrefl β (lt_of_lt_of_le hβ hcf)

def R (ξ : Ordinal.{u}) : Prop := omega < ξ ∧ IsRegular ξ

/-- A cofinal sequence shorter than a Hartogs ordinal would combine the
injections of all its initial segments into one injection of the Hartogs
ordinal.  The only cardinal-arithmetic input is an injection `X × X → X`. -/
theorem no_short_cofinal_map_to_hartogs {X : Type u} {δ : Ordinal.{u}}
    (hδ : δ < hartogs X) (g : (representative δ).Carrier → Ordinal.{u})
    (hg : ∀ i, g i < hartogs X) (hgsup : sup g = hartogs X)
    (pair : X × X → X) (hpair : ∀ a b, pair a = pair b → a = b) : False := by
  classical
  let θ := hartogs X
  obtain ⟨q, hq⟩ := (lt_hartogs_iff_injective X δ).mp hδ
  let rank : (representative θ).Carrier → Ordinal.{u} := fun x =>
    type ((representative θ).below x)
  have hindex (x : (representative θ).Carrier) :
      ∃ i, rank x < g i := by
    have hlt : rank x < sup g := by
      rw [hgsup]
      exact initial_lt θ x
    exact (lt_sup_iff g (rank x)).mp hlt
  let index (x : (representative θ).Carrier) : (representative δ).Carrier :=
    Classical.choose (hindex x)
  have hindex_spec (x : (representative θ).Carrier) : rank x < g (index x) :=
    Classical.choose_spec (hindex x)
  let embed (i : (representative δ).Carrier) :
      (representative (g i)).Carrier → X :=
    Classical.choose (injective_of_lt_hartogs (hg i))
  have hembed (i : (representative δ).Carrier) :
      ∀ a b, embed i a = embed i b → a = b :=
    Classical.choose_spec (injective_of_lt_hartogs (hg i))
  let Packed := Sigma fun i : (representative δ).Carrier =>
    (representative (g i)).Carrier
  let pack (p : Packed) : X × X :=
    (q p.1, embed p.1 p.2)
  have hpack : ∀ p r : Packed, pack p = pack r → p = r := by
    intro p r hpr
    cases p with
    | mk i a =>
      cases r with
      | mk j b =>
        have hi : i = j := hq _ _ (congrArg Prod.fst hpr)
        subst j
        have hab : a = b := hembed i a b (congrArg Prod.snd hpr)
        subst b
        rfl
  let point (x : (representative θ).Carrier) :
      (representative (g (index x))).Carrier :=
    Classical.choose (initial_surjective (g (index x)) (rank x) (hindex_spec x))
  have hpoint (x : (representative θ).Carrier) :
      rank x = type ((representative (g (index x))).below (point x)) :=
    Classical.choose_spec (initial_surjective (g (index x)) (rank x) (hindex_spec x))
  let code (x : (representative θ).Carrier) : X :=
    pair (pack ⟨index x, point x⟩)
  have hcode : ∀ x y, code x = code y → x = y := by
    intro x y hxy
    have hp := hpair _ _ hxy
    have hσ := hpack _ _ hp
    let measure (p : Packed) : Ordinal.{u} :=
      type ((representative (g p.1)).below p.2)
    have hrank := calc
      rank x = measure ⟨index x, point x⟩ := hpoint x
      _ = measure ⟨index y, point y⟩ := congrArg measure hσ
      _ = rank y := (hpoint y).symm
    exact initial_injective θ x y hrank
  exact no_injection_hartogs X code hcode

/-- Hartogs is regular when the underlying type admits an injective pairing.
The lemma above supplies the cofinality part; `hlim` supplies the limit part. -/
theorem hartogs_regular_of_pair_injective {X : Type u}
    (hlim : IsLimit (hartogs X)) (pair : X × X → X)
    (hpair : ∀ a b, pair a = pair b → a = b) : IsRegular (hartogs X) := by
  let θ := hartogs X
  have hcofinal : CofinalFrom θ θ := by
    let f : (representative θ).Carrier → Ordinal.{u} := fun x =>
      type ((representative θ).below x)
    have hlt : ∀ x, f x < θ := fun x => initial_lt θ x
    have hsup : sup f = θ := by
      apply le_antisymm
      · apply (sup_le_iff f θ).mpr
        intro x
        exact Or.inl (hlt x)
      · apply (not_lt_iff_le (sup f) θ).mp
        intro hsupθ
        let ξ := sup f
        have hξθ : ξ < θ := by simpa [ξ] using hsupθ
        obtain ⟨x, hx⟩ := initial_surjective θ (succ ξ) (hlim.2 ξ hξθ)
        have hvalue : f x = succ ξ := by simpa [f] using hx.symm
        have hle : succ ξ ≤ sup f := by
          simpa only [hvalue] using le_sup f x
        have hle' : succ ξ ≤ ξ := by simpa [ξ] using hle
        exact lt_irrefl ξ (lt_of_lt_of_le (lt_succ_self ξ) hle')
    exact ⟨f, hlt, hsup⟩
  have hcf_le : cf θ ≤ θ := least_le _ hcofinal
  have hθ_le_cf : θ ≤ cf θ := by
    apply (not_lt_iff_le (cf θ) θ).mp
    intro hcf_lt
    have hcf_def : CofinalFrom (cf θ) θ := by
      unfold cf
      exact (least_spec (fun β => CofinalFrom β θ)
        (Exists.intro θ hcofinal)).1
    obtain ⟨g, hg, hgsup⟩ := hcf_def
    exact no_short_cofinal_map_to_hartogs hcf_lt g hg hgsup pair hpair
  exact ⟨hlim, le_antisymm hcf_le hθ_le_cf⟩

/-- The Hartogs ordinal of the representative of `η` lies strictly above `η`
and no higher than any regular ordinal `κ` above `η`.  In `Setting.lean`, the
partition property strengthens this to a strict upper bound below a weakly
compact ordinal. -/
theorem IsRegular.hartogs_bounds {κ η : Ordinal.{u}} (hκ : IsRegular κ)
    (hη : η < κ) :
    η < hartogs (representative η).Carrier ∧ hartogs (representative η).Carrier ≤ κ := by
  constructor
  · apply lt_hartogs_of_injective η (fun x => x)
    intro x y h
    exact h
  · apply (not_lt_iff_le _ _).mp
    intro hk
    obtain ⟨f, hf⟩ := (lt_hartogs_iff_injective (representative η).Carrier κ).mp hk
    exact hκ.no_injective_to_smaller hη f hf

theorem isLimit_iff_not (α : Ordinal.{u}) (h0 : α ≠ 0) (hs : ¬ ∃ β, α = succ β) : IsLimit α := by
  apply And.intro (pos_of_ne_zero h0)
  intro β hβ
  cases succ_le_of_lt hβ with
  | inl h => exact h
  | inr h => exact absurd (Exists.intro β h.symm) hs

theorem zero_or_succ_or_limit (α : Ordinal.{u}) :
    α = 0 ∨ (∃ β, α = succ β) ∨ IsLimit α := by
  cases Classical.em (α = 0) with
  | inl h => exact Or.inl h
  | inr h0 =>
    cases Classical.em (∃ β, α = succ β) with
    | inl hs => exact Or.inr (Or.inl hs)
    | inr hs => exact Or.inr (Or.inr (isLimit_iff_not α h0 hs))

theorem IsLimit.succ_lt {α β : Ordinal.{u}} (h : IsLimit α) (hβ : β < α) : succ β < α :=
  h.2 β hβ

theorem IsLimit.ne_succ {α : Ordinal.{u}} (h : IsLimit α) (β : Ordinal.{u}) : α ≠ succ β := by
  intro e
  have := h.2 β (by rw [e]; exact lt_succ_self β)
  rw [e] at this
  exact lt_irrefl _ this

theorem ordNat_succ (n : Nat) : ordNat.{u} (n + 1) = succ (ordNat n) := rfl

theorem ordNat_zero : ordNat.{u} 0 = 0 := rfl

theorem ordNat_lt {m n : Nat} (h : m < n) : ordNat.{u} m < ordNat n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rw [ordNat_succ]
    cases Nat.lt_succ_iff_lt_or_eq.mp h with
    | inl h' => exact lt_trans _ _ _ (ih h') (lt_succ_self _)
    | inr h' =>
      rw [h']
      exact lt_succ_self _

theorem ordNat_le {m n : Nat} (h : m ≤ n) : ordNat.{u} m ≤ ordNat n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h' => exact Or.inl (ordNat_lt h')
  | inr h' =>
    rw [h']
    exact le_refl _

theorem ordNat_le_iff {m n : Nat} : ordNat.{u} m ≤ ordNat n ↔ m ≤ n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge n m with
    | inl h' => exact absurd h (not_le_of_lt (ordNat_lt h'))
    | inr h' => exact h'
  · exact ordNat_le

theorem ordNat_injective {m n : Nat} (h : ordNat.{u} m = ordNat n) : m = n := by
  apply Nat.le_antisymm
  · apply ordNat_le_iff.mp
    rw [h]
    exact le_refl _
  · apply ordNat_le_iff.mp
    rw [h]
    exact le_refl _

theorem ordNat_lt_omega (n : Nat) : ordNat.{u} n < omega :=
  lt_of_lt_of_le (ordNat_lt (Nat.lt_succ_self n))
    (le_sup (fun k : ULift.{u} Nat => ordNat k.down) (ULift.up (n + 1)))

theorem lt_ordNat_iff {a : Ordinal.{u}} {n : Nat} : a < ordNat n ↔ ∃ m, m < n ∧ a = ordNat m := by
  apply Iff.intro
  · intro h
    induction n with
    | zero => exact absurd h (not_lt_zero a)
    | succ n ih =>
      cases le_of_lt_succ h with
      | inl h' =>
        cases ih h' with
        | intro m hm => exact Exists.intro m (And.intro (Nat.lt_succ_of_lt hm.1) hm.2)
      | inr h' => exact Exists.intro n (And.intro (Nat.lt_succ_self n) h')
  · intro h
    cases h with
    | intro m hm =>
      rw [hm.2]
      exact ordNat_lt hm.1

theorem lt_omega_iff (a : Ordinal.{u}) : a < omega ↔ ∃ n, a = ordNat n := by
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ a).mp h with
    | intro k hk =>
      cases lt_ordNat_iff.mp hk with
      | intro m hm => exact Exists.intro m hm.2
  · intro h
    cases h with
    | intro n hn =>
      rw [hn]
      exact ordNat_lt_omega n

theorem isLimit_omega : IsLimit (omega : Ordinal.{u}) := by
  apply And.intro
  · have h := ordNat_lt_omega.{u} 0
    rw [ordNat_zero] at h
    exact h
  · intro β hβ
    cases (lt_omega_iff β).mp hβ with
    | intro n hn =>
      rw [hn, ← ordNat_succ]
      exact ordNat_lt_omega (n + 1)

theorem zero_lt_omega : (0 : Ordinal.{u}) < omega := isLimit_omega.1

/-- Every infinite ordinal is equinumerous with its successor. -/
theorem exists_injective_succ_into_of_omega_le {β : Ordinal.{u}}
    (hω : omega ≤ β) :
    ∃ f : (representative (succ β)).Carrier → (representative β).Carrier,
      ∀ x y, f x = f y → x = y := by
  classical
  let code (ξ : Ordinal.{u}) : Ordinal.{u} :=
    if htop : ξ = β then 0 else if hfinite : ξ < omega then succ ξ else ξ
  have hcode_lt {ξ : Ordinal.{u}} (hξ : ξ < succ β) : code ξ < β := by
    have hξle : ξ ≤ β := (lt_succ_iff_le ξ β).mp hξ
    by_cases htop : ξ = β
    · simp [code, htop]
      exact lt_of_lt_of_le zero_lt_omega hω
    · have hξβ : ξ < β := by
        cases hξle with
        | inl h => exact h
        | inr h => exact False.elim (htop h)
      by_cases hfinite : ξ < omega
      · simp [code, htop, hfinite]
        exact lt_of_lt_of_le (isLimit_omega.2 ξ hfinite) hω
      · simp [code, htop, hfinite]
        exact hξβ
  have hcode_pos {ξ : Ordinal.{u}} (hξ : ξ < β) : 0 < code ξ := by
    have hnot : ξ ≠ β := ne_of_lt hξ
    by_cases hfinite : ξ < omega
    · have hc : code ξ = succ ξ := by simp [code, hnot, hfinite]
      rw [hc]
      exact zero_lt_succ ξ
    · have hc : code ξ = ξ := by simp [code, hnot, hfinite]
      rw [hc]
      exact lt_of_lt_of_le zero_lt_omega ((not_lt_iff_le ξ omega).mp hfinite)
  have hcode_inj {ξ ζ : Ordinal.{u}} (hξ : ξ < succ β) (hζ : ζ < succ β)
      (heq : code ξ = code ζ) : ξ = ζ := by
    have hξle : ξ ≤ β := (lt_succ_iff_le ξ β).mp hξ
    have hζle : ζ ≤ β := (lt_succ_iff_le ζ β).mp hζ
    by_cases hξtop : ξ = β
    · subst ξ
      by_cases hζtop : ζ = β
      · exact hζtop.symm
      · have hζβ : ζ < β := by
          cases hζle with
          | inl h => exact h
          | inr h => exact False.elim (hζtop h)
        have hpos := hcode_pos hζβ
        have hzero : code β = 0 := by simp [code]
        rw [hzero] at heq
        exact False.elim (ne_of_gt hpos heq.symm)
    · have hξβ : ξ < β := by
        cases hξle with
        | inl h => exact h
        | inr h => exact False.elim (hξtop h)
      by_cases hζtop : ζ = β
      · subst ζ
        have hpos := hcode_pos hξβ
        have hzero : code β = 0 := by simp [code]
        rw [hzero] at heq
        exact False.elim (ne_of_gt hpos heq)
      · have hζβ : ζ < β := by
          cases hζle with
          | inl h => exact h
          | inr h => exact False.elim (hζtop h)
        by_cases hξfinite : ξ < omega
        · by_cases hζfinite : ζ < omega
          · have hξcode : code ξ = succ ξ := by simp [code, ne_of_lt hξβ, hξfinite]
            have hζcode : code ζ = succ ζ := by simp [code, ne_of_lt hζβ, hζfinite]
            rw [hξcode, hζcode] at heq
            apply le_antisymm
            · exact (lt_succ_iff_le ξ ζ).mp (heq ▸ lt_succ_self ξ)
            · exact (lt_succ_iff_le ζ ξ).mp (heq.symm ▸ lt_succ_self ζ)
          · have hleft : code ξ < omega := by
              rw [show code ξ = succ ξ from by
                simp [code, ne_of_lt hξβ, hξfinite]]
              exact isLimit_omega.2 ξ hξfinite
            have hright : omega ≤ code ζ := by
              rw [show code ζ = ζ from by
                simp [code, ne_of_lt hζβ, hζfinite]]
              exact (not_lt_iff_le ζ omega).mp hζfinite
            have hright' : omega ≤ code ξ := by rw [heq]; exact hright
            exact False.elim (not_lt_of_le hright' hleft)
        · by_cases hζfinite : ζ < omega
          · have hleft : omega ≤ code ξ := by
              rw [show code ξ = ξ from by
                simp [code, ne_of_lt hξβ, hξfinite]]
              exact (not_lt_iff_le ξ omega).mp hξfinite
            have hright : code ζ < omega := by
              rw [show code ζ = succ ζ from by
                simp [code, ne_of_lt hζβ, hζfinite]]
              exact isLimit_omega.2 ζ hζfinite
            have hleft' : omega ≤ code ζ := by rw [heq] at hleft; exact hleft
            exact False.elim (not_lt_of_le hleft' hright)
          · have hξcode : code ξ = ξ := by simp [code, ne_of_lt hξβ, hξfinite]
            have hζcode : code ζ = ζ := by simp [code, ne_of_lt hζβ, hζfinite]
            rw [hξcode, hζcode] at heq
            exact heq
  let f (x : (representative (succ β)).Carrier) :
      (representative β).Carrier :=
    Classical.choose (initial_surjective β (code (type ((representative (succ β)).below x)))
      (hcode_lt (initial_lt (succ β) x)))
  have hf_spec (x : (representative (succ β)).Carrier) :
      code (type ((representative (succ β)).below x)) =
        type ((representative β).below (f x)) :=
    Classical.choose_spec (initial_surjective β
      (code (type ((representative (succ β)).below x)))
      (hcode_lt (initial_lt (succ β) x)))
  refine ⟨f, ?_⟩
  intro x y hxy
  have hrank : code (type ((representative (succ β)).below x)) =
      code (type ((representative (succ β)).below y)) := by
    calc
      _ = type ((representative β).below (f x)) := hf_spec x
      _ = type ((representative β).below (f y)) :=
        congrArg (fun z => type ((representative β).below z)) hxy
      _ = _ := (hf_spec y).symm
  exact initial_injective (succ β) x y
    (hcode_inj (initial_lt (succ β) x) (initial_lt (succ β) y) hrank)

/-- Hartogs of an infinite type is a limit ordinal.  If it were a successor,
the predecessor embeds into the type and its successor embeds back into the
predecessor by shifting the finite initial segment. -/
theorem hartogs_isLimit_of_omega_lt {X : Type u} (hω : omega < hartogs X) :
    IsLimit (hartogs X) := by
  let θ := hartogs X
  apply isLimit_iff_not θ
    (ne_of_gt (lt_trans 0 omega (hartogs X) zero_lt_omega hω))
  intro hsucc
  obtain ⟨β, hθ⟩ := hsucc
  have hβθ : β < θ := by rw [hθ]; exact lt_succ_self β
  have hωβ : omega ≤ β := by
    apply (lt_succ_iff_le omega β).mp
    rw [← hθ]
    exact hω
  obtain ⟨shift, hshift⟩ := exists_injective_succ_into_of_omega_le hωβ
  obtain ⟨embed, hembed⟩ := (lt_hartogs_iff_injective X β).mp hβθ
  let iso := representativeOrderIso (representative θ)
    ((type_representative θ).trans hθ)
  let f : (representative θ).Carrier → X := fun x => embed (shift (iso.toFun x))
  have hf : ∀ x y, f x = f y → x = y := by
    intro x y hxy
    have h1 := hembed _ _ hxy
    have h2 := hshift _ _ h1
    have h3 := congrArg iso.invFun h2
    simpa only [iso.left_inv] using h3
  exact no_injection_hartogs X f hf

def natOf (a : Ordinal.{u}) : Nat :=
  open Classical in
  if h : ∃ n, a = ordNat n then Classical.choose h else 0

theorem natOf_ordNat (n : Nat) : natOf (ordNat.{u} n) = n := by
  have h : ∃ m, ordNat.{u} n = ordNat m := Exists.intro n rfl
  unfold natOf
  rw [dite_eq_left h]
  exact (ordNat_injective (Classical.choose_spec h)).symm

def IsPrincipal (α : Ordinal.{u}) : Prop := α ≠ 0 ∧ AddPrincipal α

theorem IsPrincipal.pos {α : Ordinal.{u}} (h : IsPrincipal α) : 0 < α := pos_of_ne_zero h.1

theorem isPrincipal_one : IsPrincipal (succ (0 : Ordinal.{u})) :=
  And.intro (succ_ne_zero 0) succ_zero_principal

theorem IsPrincipal.add_eq {p x y : Ordinal.{u}} (hp : IsPrincipal p) (h : x + y = p) :
    (x = p ∧ y = 0) ∨ y = p := by
  have hx : x ≤ p := by
    rw [← h]
    exact le_add x y
  have hy : y ≤ p := by
    rw [← h]
    exact right_le_add x y
  cases hy with
  | inr hy => exact Or.inr hy
  | inl hy =>
    cases hx with
    | inl hx =>
      have := hp.2 x y hx hy
      rw [h] at this
      exact absurd this (lt_irrefl p)
    | inr hx =>
      apply Or.inl
      apply And.intro hx
      apply add_right_cancel (a := x)
      rw [add_zero, h, hx]

theorem IsPrincipal.succ_lt {p x : Ordinal.{u}} (hp : IsPrincipal p) (h1 : succ 0 < p)
    (hx : x < p) : succ x < p := by
  rw [← add_one_eq_succ]
  exact hp.2 x _ hx h1

theorem IsPrincipal.isLimit {p : Ordinal.{u}} (hp : IsPrincipal p) (h1 : succ 0 < p) :
    IsLimit p :=
  And.intro hp.pos (fun _ hx => hp.succ_lt h1 hx)

theorem addPrincipal_of_limit {p : Ordinal.{u}}
    (h : ∀ η, η < p → ∃ q, AddPrincipal q ∧ η < q ∧ q ≤ p) : AddPrincipal p := by
  intro x y hx hy
  cases le_total x y with
  | inl hxy =>
    cases h y hy with
    | intro q hq => exact lt_of_lt_of_le (hq.1 x y (lt_of_le_of_lt hxy hq.2.1) hq.2.1) hq.2.2
  | inr hyx =>
    cases h x hx with
    | intro q hq => exact lt_of_lt_of_le (hq.1 x y hq.2.1 (lt_of_le_of_lt hyx hq.2.1)) hq.2.2

theorem IsRegular.isLimit {κ : Ordinal.{u}} (h : IsRegular κ) : IsLimit κ := h.1

theorem IsRegular.pos {κ : Ordinal.{u}} (h : IsRegular κ) : 0 < κ := h.1.1

theorem IsRegular.supLt_lt {κ β : Ordinal.{u}} (hκ : IsRegular κ) (hβ : β < κ)
    {F : Ordinal.{u} → Ordinal.{u}} (hF : ∀ ξ, ξ < β → F ξ < κ) : supLt β F < κ := by
  have hle : supLt β F ≤ κ := (supLt_le_iff β F κ).mpr (fun ξ hξ => Or.inl (hF ξ hξ))
  cases hle with
  | inl h => exact h
  | inr h =>
    have hcof : CofinalFrom β κ :=
      Exists.intro (fun x => F (type ((representative β).below x)))
        (And.intro (fun x => hF _ (initial_lt β x)) h)
    have hcf : cf κ ≤ β := least_le _ hcof
    rw [hκ.2] at hcf
    exact absurd hβ (not_lt_of_le hcf)

theorem IsRegular.add_lt {κ a b : Ordinal.{u}} (hκ : IsRegular κ) (ha : a < κ) (hb : b < κ) :
    a + b < κ := by
  apply lt_of_not_le
  intro hle
  cases le_add_cases a b κ hle (not_lt_of_le (le_of_lt ha)) with
  | intro d hd =>
    have hdκ : d < κ := lt_of_le_of_lt hd.1 hb
    cases zero_or_succ_or_limit d with
    | inl h0 =>
      have := hd.2
      rw [h0, add_zero] at this
      rw [this] at ha
      exact lt_irrefl a ha
    | inr h =>
      cases h with
      | inl hs =>
        cases hs with
        | intro e he =>
          have := hd.2
          rw [he, add_succ] at this
          exact hκ.isLimit.ne_succ _ this
      | inr hl =>
        have hsup : κ ≤ supLt d (fun x => a + x) := by
          apply le_of_not_lt
          intro hlt
          rw [hd.2] at hlt
          cases (lt_add_iff a d _).mp hlt with
          | inl hlta =>
            have : a + 0 ≤ supLt d (fun x => a + x) := le_supLt d _ hl.1
            rw [add_zero] at this
            exact not_lt_of_le this hlta
          | inr hx =>
            cases hx with
            | intro x hx =>
              have h1 : a + succ x ≤ supLt d (fun x => a + x) := le_supLt d _ (hl.2 x hx.1)
              rw [add_succ] at h1
              exact not_lt_of_le hx.2 (lt_of_lt_of_le (lt_succ_self _) h1)
        have hlt : supLt d (fun x => a + x) < κ := by
          apply hκ.supLt_lt hdκ
          intro ξ hξ
          rw [hd.2]
          exact add_lt_add_right a hξ
        exact not_lt_of_le hsup hlt

theorem IsRegular.addPrincipal {κ : Ordinal.{u}} (hκ : IsRegular κ) : AddPrincipal κ :=
  fun _ _ ha hb => hκ.add_lt ha hb

theorem IsRegular.isPrincipal {κ : Ordinal.{u}} (hκ : IsRegular κ) : IsPrincipal κ :=
  And.intro (ne_of_gt hκ.pos) hκ.addPrincipal

def mul (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun b ih =>
    sup (fun x : (representative b).Carrier =>
      ih (type ((representative b).below x)) (initial_lt b x) + a))

theorem mul_eq (a b : Ordinal.{u}) : mul a b = supLt b (fun ξ => mul a ξ + a) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem mul_add_le {a x b : Ordinal.{u}} (h : x < b) : mul a x + a ≤ mul a b := by
  rw [mul_eq a b]
  exact le_supLt b (fun ξ => mul a ξ + a) h

theorem mul_pair_lt {a b x y : Ordinal.{u}} (hx : x < b) (hy : y < a) :
    mul a x + y < mul a b :=
  lt_of_lt_of_le (add_lt_add_right _ hy) (mul_add_le hx)

theorem mul_pair_inj {a x x' y y' : Ordinal.{u}} (hy : y < a) (hy' : y' < a)
    (h : mul a x + y = mul a x' + y') : x = x' ∧ y = y' := by
  have hx : x = x' := by
    cases lt_total x x' with
    | inl hlt =>
      have h1 := lt_of_lt_of_le (mul_pair_lt (b := x') (a := a) hlt hy) (le_add _ y')
      rw [h] at h1
      exact absurd h1 (lt_irrefl _)
    | inr h' =>
      cases h' with
      | inl e => exact e
      | inr hlt =>
        have h1 := lt_of_lt_of_le (mul_pair_lt (b := x) (a := a) hlt hy') (le_add _ y)
        rw [h] at h1
        exact absurd h1 (lt_irrefl _)
  apply And.intro hx
  rw [hx] at h
  exact add_right_cancel h

theorem IsRegular.mul_lt {κ a b : Ordinal.{u}} (hκ : IsRegular κ) (ha : a < κ) (hb : b < κ) :
    mul a b < κ := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    rw [mul_eq]
    apply hκ.supLt_lt hb
    intro ξ hξ
    exact hκ.add_lt (ih ξ hξ (lt_trans ξ b κ hξ hb)) ha

def Small (κ : Ordinal.{u}) (A : Ordinal.{u} → Prop) : Prop :=
  ∃ β, β < κ ∧ ∃ f : Ordinal.{u} → Ordinal.{u},
    (∀ x, A x → f x < β) ∧ ∀ x y, A x → A y → f x = f y → x = y

theorem Small.mono {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (h : Small κ B)
    (hAB : ∀ x, A x → B x) : Small κ A := by
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      exact Exists.intro β (And.intro hβ.1 (Exists.intro f (And.intro
        (fun x hx => hf.1 x (hAB x hx))
        (fun x y hx hy e => hf.2 x y (hAB x hx) (hAB y hy) e))))

theorem small_lt {κ β : Ordinal.{u}} (hβ : β < κ) : Small κ (fun x => x < β) :=
  Exists.intro β (And.intro hβ (Exists.intro (fun x => x) (And.intro
    (fun _ hx => hx) (fun _ _ _ _ e => e))))

theorem Small.union {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (hκ : IsRegular κ)
    (hA : Small κ A) (hB : Small κ B) : Small κ (fun x => A x ∨ B x) := by
  classical
  cases hA with
  | intro βA hA =>
    cases hA.2 with
    | intro fA hfA =>
      cases hB with
      | intro βB hB =>
        cases hB.2 with
        | intro fB hfB =>
          refine Exists.intro (βA + βB) (And.intro (hκ.add_lt hA.1 hB.1) ?_)
          refine Exists.intro (fun x => if A x then fA x else βA + fB x) (And.intro ?_ ?_)
          · intro x hx
            by_cases hAx : A x
            · simp only [hAx, ↓reduceIte]
              exact lt_of_lt_of_le (hfA.1 x hAx) (le_add βA βB)
            · simp only [hAx, ↓reduceIte]
              cases hx with
              | inl h => exact absurd h hAx
              | inr h => exact add_lt_add_right βA (hfB.1 x h)
          · intro x y hx hy e
            by_cases hAx : A x
            · by_cases hAy : A y
              · simp only [hAx, hAy, ↓reduceIte] at e
                exact hfA.2 x y hAx hAy e
              · simp only [hAx, hAy, ↓reduceIte] at e
                have := lt_of_lt_of_le (hfA.1 x hAx) (le_add βA (fB y))
                rw [e] at this
                exact absurd this (lt_irrefl _)
            · by_cases hAy : A y
              · simp only [hAx, hAy, ↓reduceIte] at e
                have := lt_of_lt_of_le (hfA.1 y hAy) (le_add βA (fB x))
                rw [← e] at this
                exact absurd this (lt_irrefl _)
              · simp only [hAx, hAy, ↓reduceIte] at e
                have hBx : B x := by
                  cases hx with
                  | inl h => exact absurd h hAx
                  | inr h => exact h
                have hBy : B y := by
                  cases hy with
                  | inl h => exact absurd h hAy
                  | inr h => exact h
                exact hfB.2 x y hBx hBy (add_right_cancel e)

theorem Small.image {κ : Ordinal.{u}} {A : Ordinal.{u} → Prop} (hA : Small κ A)
    (g : Ordinal.{u} → Ordinal.{u}) : Small κ (fun z => ∃ x, A x ∧ z = g x) := by
  classical
  cases hA with
  | intro β hA =>
    cases hA.2 with
    | intro f hf =>
      let pre : Ordinal.{u} → Ordinal.{u} := fun z =>
        if h : ∃ x, A x ∧ z = g x then Classical.choose h else 0
      have hpre : ∀ z (h : ∃ x, A x ∧ z = g x), A (pre z) ∧ z = g (pre z) := by
        intro z h
        have e : pre z = Classical.choose h := dite_eq_left h
        rw [e]
        exact Classical.choose_spec h
      refine Exists.intro β (And.intro hA.1 (Exists.intro (fun z => f (pre z)) (And.intro ?_ ?_)))
      · intro z hz
        exact hf.1 _ (hpre z hz).1
      · intro z w hz hw e
        have := hf.2 _ _ (hpre z hz).1 (hpre w hw).1 e
        rw [(hpre z hz).2, (hpre w hw).2, this]

theorem Small.image2 {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (hκ : IsRegular κ)
    (hA : Small κ A) (hB : Small κ B) (g : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    Small κ (fun z => ∃ x y, A x ∧ B y ∧ z = g x y) := by
  classical
  cases hA with
  | intro βA hA =>
    cases hA.2 with
    | intro fA hfA =>
      cases hB with
      | intro βB hB =>
        cases hB.2 with
        | intro fB hfB =>
          let P : Ordinal.{u} → Prop := fun z => ∃ x y, A x ∧ B y ∧ z = g x y
          let preA : Ordinal.{u} → Ordinal.{u} := fun z =>
            if h : P z then Classical.choose h else 0
          let preB : Ordinal.{u} → Ordinal.{u} := fun z =>
            if h : P z then Classical.choose (Classical.choose_spec h) else 0
          have hpre : ∀ z, P z → A (preA z) ∧ B (preB z) ∧ z = g (preA z) (preB z) := by
            intro z h
            have e1 : preA z = Classical.choose h := dite_eq_left h
            have e2 : preB z = Classical.choose (Classical.choose_spec h) := dite_eq_left h
            rw [e1, e2]
            exact Classical.choose_spec (Classical.choose_spec h)
          refine Exists.intro (mul βA βB) (And.intro (hκ.mul_lt hA.1 hB.1) ?_)
          refine Exists.intro (fun z => mul βA (fB (preB z)) + fA (preA z)) (And.intro ?_ ?_)
          · intro z hz
            exact mul_pair_lt (hfB.1 _ (hpre z hz).2.1) (hfA.1 _ (hpre z hz).1)
          · intro z w hz hw e
            have hp := mul_pair_inj (hfA.1 _ (hpre z hz).1) (hfA.1 _ (hpre w hw).1) e
            have eB := hfB.2 _ _ (hpre z hz).2.1 (hpre w hw).2.1 hp.1
            have eA := hfA.2 _ _ (hpre z hz).1 (hpre w hw).1 hp.2
            rw [(hpre z hz).2.2, (hpre w hw).2.2, eA, eB]

theorem Small.iUnion {κ : Ordinal.{u}} {I : Ordinal.{u} → Prop}
    {A : Ordinal.{u} → Ordinal.{u} → Prop} (hκ : IsRegular κ) (hI : Small κ I)
    (hA : ∀ i, I i → Small κ (A i)) : Small κ (fun z => ∃ i, I i ∧ A i z) := by
  classical
  cases hI with
  | intro βI hI =>
    cases hI.2 with
    | intro fI hfI =>
      let bnd : Ordinal.{u} → Ordinal.{u} := fun i =>
        if h : I i then Classical.choose (hA i h) else 0
      let enc : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} := fun i =>
        if h : I i then Classical.choose (Classical.choose_spec (hA i h)).2 else fun _ => 0
      have hbnd : ∀ i, bnd i < κ := by
        intro i
        by_cases h : I i
        · have e : bnd i = Classical.choose (hA i h) := dite_eq_left h
          rw [e]
          exact (Classical.choose_spec (hA i h)).1
        · have e : bnd i = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      have henc : ∀ i, I i → (∀ x, A i x → enc i x < bnd i) ∧
          ∀ x y, A i x → A i y → enc i x = enc i y → x = y := by
        intro i h
        have e1 : bnd i = Classical.choose (hA i h) := dite_eq_left h
        have e2 : enc i = Classical.choose (Classical.choose_spec (hA i h)).2 := dite_eq_left h
        rw [e1, e2]
        exact Classical.choose_spec (Classical.choose_spec (hA i h)).2
      let inv : Ordinal.{u} → Ordinal.{u} := fun y =>
        if h : ∃ i, I i ∧ fI i = y then Classical.choose h else 0
      have hinv : ∀ i, I i → inv (fI i) = i := by
        intro i hi
        have h : ∃ j, I j ∧ fI j = fI i := Exists.intro i (And.intro hi rfl)
        have e : inv (fI i) = Classical.choose h := dite_eq_left h
        rw [e]
        exact hfI.2 _ _ (Classical.choose_spec h).1 hi (Classical.choose_spec h).2
      let γ := supLt βI (fun y => bnd (inv y))
      have hγ : γ < κ := hκ.supLt_lt hI.1 (fun y _ => hbnd (inv y))
      have hbndγ : ∀ i, I i → bnd i ≤ γ := by
        intro i hi
        have := le_supLt βI (fun y => bnd (inv y)) (hfI.1 i hi)
        rw [hinv i hi] at this
        exact this
      let idx : Ordinal.{u} → Ordinal.{u} := fun z =>
        if h : ∃ i, I i ∧ A i z then Classical.choose h else 0
      have hidx : ∀ z, (∃ i, I i ∧ A i z) → I (idx z) ∧ A (idx z) z := by
        intro z h
        have e : idx z = Classical.choose h := dite_eq_left h
        rw [e]
        exact Classical.choose_spec h
      refine Exists.intro (mul γ βI) (And.intro (hκ.mul_lt hγ hI.1) ?_)
      refine Exists.intro (fun z => mul γ (fI (idx z)) + enc (idx z) z) (And.intro ?_ ?_)
      · intro z hz
        have hi := hidx z hz
        exact mul_pair_lt (hfI.1 _ hi.1)
          (lt_of_lt_of_le ((henc _ hi.1).1 z hi.2) (hbndγ _ hi.1))
      · intro z w hz hw e
        have hiz := hidx z hz
        have hiw := hidx w hw
        have hp := mul_pair_inj
          (lt_of_lt_of_le ((henc _ hiz.1).1 z hiz.2) (hbndγ _ hiz.1))
          (lt_of_lt_of_le ((henc _ hiw.1).1 w hiw.2) (hbndγ _ hiw.1)) e
        have ei : idx z = idx w := hfI.2 _ _ hiz.1 hiw.1 hp.1
        have he := hp.2
        rw [ei] at he
        rw [ei] at hiz
        exact (henc _ hiw.1).2 z w hiz.2 hiw.2 he

theorem small_natOrd {κ : Ordinal.{u}} (hω : omega < κ) :
    Small κ (fun x => ∃ n, x = ordNat n) :=
  (small_lt hω).mono (fun x hx => (lt_omega_iff x).mpr hx)

def listSum : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | a :: l => a + listSum l

theorem listSum_nil : listSum ([] : List Ordinal.{u}) = 0 := rfl

theorem listSum_cons (a : Ordinal.{u}) (l : List Ordinal.{u}) :
    listSum (a :: l) = a + listSum l := rfl

theorem listSum_append (l₁ l₂ : List Ordinal.{u}) :
    listSum (l₁ ++ l₂) = listSum l₁ + listSum l₂ := by
  induction l₁ with
  | nil => exact (zero_add _).symm
  | cons a l ih =>
    show a + listSum (l ++ l₂) = (a + listSum l) + listSum l₂
    rw [ih, add_assoc]

theorem le_listSum_of_mem {l : List Ordinal.{u}} {p : Ordinal.{u}} (h : p ∈ l) :
    p ≤ listSum l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
    cases List.mem_cons.mp h with
    | inl h => rw [h]; exact le_add a _
    | inr h => exact le_trans (ih h) (right_le_add a _)

theorem listSum_lt {q : Ordinal.{u}} (hq : IsPrincipal q) {l : List Ordinal.{u}}
    (h : ∀ p, p ∈ l → p < q) : listSum l < q := by
  induction l with
  | nil => exact hq.pos
  | cons a l ih =>
    exact hq.2 a _ (h a (List.mem_cons_self))
      (ih (fun p hp => h p (List.mem_cons_of_mem a hp)))

def Nonincr (l : List Ordinal.{u}) : Prop := l.Pairwise (fun a b => b ≤ a)

def CNF (α : Ordinal.{u}) (l : List Ordinal.{u}) : Prop :=
  (∀ p, p ∈ l → IsPrincipal p) ∧ Nonincr l ∧ α = listSum l

theorem cnf_zero : CNF (0 : Ordinal.{u}) [] :=
  And.intro (fun _ h => absurd h List.not_mem_nil) (And.intro List.Pairwise.nil rfl)

theorem cnf_single {p : Ordinal.{u}} (hp : IsPrincipal p) : CNF p [p] := by
  refine And.intro ?_ (And.intro (List.pairwise_singleton _ p) (add_zero p).symm)
  intro q hq
  rw [List.mem_singleton.mp hq]
  exact hp

theorem CNF.principal {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) {p : Ordinal.{u}}
    (hp : p ∈ l) : IsPrincipal p := h.1 p hp

theorem CNF.le {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) {p : Ordinal.{u}}
    (hp : p ∈ l) : p ≤ α := by
  rw [h.2.2]
  exact le_listSum_of_mem hp

theorem CNF.tail {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) :
    CNF (listSum l) l :=
  And.intro (fun q hq => h.1 q (List.mem_cons_of_mem p hq))
    (And.intro (List.pairwise_cons.mp h.2.1).2 rfl)

theorem CNF.head_principal {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) :
    IsPrincipal p := h.1 p List.mem_cons_self

theorem CNF.head_ge {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    {q : Ordinal.{u}} (hq : q ∈ l) : q ≤ p := (List.pairwise_cons.mp h.2.1).1 q hq

theorem CNF.mem_le_head {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    {q : Ordinal.{u}} (hq : q ∈ p :: l) : q ≤ p := by
  cases List.mem_cons.mp hq with
  | inl e => rw [e]; exact le_refl p
  | inr hq => exact h.head_ge hq

theorem CNF.head_le {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) : p ≤ α :=
  h.le List.mem_cons_self

theorem CNF.pos {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) : 0 < α :=
  lt_of_lt_of_le h.head_principal.pos h.head_le

theorem CNF.eq {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) : α = listSum l := h.2.2

theorem CNF.lt_of_head_lt {α p q : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    (hq : IsPrincipal q) (hpq : p < q) : α < q := by
  rw [h.eq]
  exact listSum_lt hq (fun x hx => lt_of_le_of_lt (h.mem_le_head hx) hpq)

theorem CNF.head_max {α p q : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    (hq : IsPrincipal q) (hqα : q ≤ α) : q ≤ p := by
  apply le_of_not_lt
  intro hpq
  exact not_lt_of_le hqα (h.lt_of_head_lt hq hpq)

theorem exists_largest_principal (α : Ordinal.{u}) (h : α ≠ 0) :
    ∃ p, IsPrincipal p ∧ p ≤ α ∧ ∀ q, IsPrincipal q → q ≤ α → q ≤ p := by
  classical
  let F : Ordinal.{u} → Ordinal.{u} := fun x => if IsPrincipal x then x else 0
  have hF1 : ∀ x, IsPrincipal x → F x = x := by
    intro x hx
    show (if IsPrincipal x then x else 0) = x
    simp only [hx, ↓reduceIte]
  have hF0 : ∀ x, ¬ IsPrincipal x → F x = 0 := by
    intro x hx
    show (if IsPrincipal x then x else 0) = 0
    simp only [hx, ↓reduceIte]
  have hmax : ∀ q, IsPrincipal q → q ≤ α → q ≤ supLt (succ α) F := by
    intro q hq hqα
    have := le_supLt (succ α) F (lt_succ_of_le hqα)
    rw [hF1 q hq] at this
    exact this
  have hle : supLt (succ α) F ≤ α := by
    apply (supLt_le_iff _ _ _).mpr
    intro ξ hξ
    by_cases hP : IsPrincipal ξ
    · rw [hF1 ξ hP]
      exact le_of_lt_succ hξ
    · rw [hF0 ξ hP]
      exact zero_le α
  have hmem : ∀ x, x < supLt (succ α) F → ∃ ξ, IsPrincipal ξ ∧ x < ξ ∧ ξ ≤ supLt (succ α) F := by
    intro x hx
    cases (lt_supLt_iff _ _ _).mp hx with
    | intro ξ hξ =>
      by_cases hP : IsPrincipal ξ
      · rw [hF1 ξ hP] at hξ
        exact Exists.intro ξ (And.intro hP (And.intro hξ.2
          (hmax ξ hP (le_of_lt_succ hξ.1))))
      · rw [hF0 ξ hP] at hξ
        exact absurd hξ.2 (not_lt_zero x)
  refine Exists.intro (supLt (succ α) F) (And.intro (And.intro ?_ ?_) (And.intro hle hmax))
  · have h1 := hmax _ isPrincipal_one (succ_le_of_lt (pos_of_ne_zero h))
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_succ 0) h1)
  · apply addPrincipal_of_limit
    intro η hη
    cases hmem η hη with
    | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.1.2 hξ.2)

theorem cnf_exists (α : Ordinal.{u}) : ∃ l, CNF α l := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    by_cases h0 : α = 0
    · rw [h0]
      exact Exists.intro [] cnf_zero
    · cases exists_largest_principal α h0 with
      | intro p hp =>
        cases exists_add_of_le p α hp.2.1 with
        | intro β hβ =>
          have hβα : β < α := by
            apply lt_of_le_of_ne (by rw [hβ]; exact right_le_add p β)
            intro e
            have hfix : p + α = α := by
              rw [e] at hβ
              exact hβ.symm
            have h1 : succ 0 + α = α := by
              apply le_antisymm
              · have := add_mono_left (succ_le_of_lt hp.1.pos) α
                rw [hfix] at this
                exact this
              · exact right_le_add _ _
            have hstage : ∀ n, principalStage p n + α = α := by
              intro n
              induction n with
              | zero =>
                show succ p + α = α
                rw [← add_one_eq_succ, add_assoc, h1, hfix]
              | succ n ih =>
                show (principalStage p n + principalStage p n) + α = α
                rw [add_assoc, ih, ih]
            have hhull : principalHull p ≤ α := by
              apply (sup_le_iff _ α).mpr
              intro n
              have := le_add (principalStage p n.down) α
              rw [hstage] at this
              exact this
            have hP : IsPrincipal (principalHull p) :=
              And.intro (ne_of_gt (lt_of_le_of_lt (zero_le p) (lt_principalHull p)))
                (principalHull_principal p)
            exact not_lt_of_le (hp.2.2 _ hP hhull) (lt_principalHull p)
          cases ih β hβα with
          | intro l hl =>
            refine Exists.intro (p :: l) (And.intro ?_ (And.intro ?_ ?_))
            · intro q hq
              cases List.mem_cons.mp hq with
              | inl e => rw [e]; exact hp.1
              | inr hq => exact hl.1 q hq
            · apply List.pairwise_cons.mpr
              apply And.intro _ hl.2.1
              intro q hq
              exact hp.2.2 q (hl.1 q hq) (le_trans (hl.le hq)
                (by rw [hβ]; exact right_le_add p β))
            · rw [listSum_cons, ← hl.eq]
              exact hβ

theorem cnf_unique {α : Ordinal.{u}} {l l' : List Ordinal.{u}} (h : CNF α l) (h' : CNF α l') :
    l = l' := by
  induction l generalizing α l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons q r =>
      have := h'.pos
      rw [h.eq, listSum_nil] at this
      exact absurd this (lt_irrefl 0)
  | cons p r ih =>
    cases l' with
    | nil =>
      have := h.pos
      rw [h'.eq, listSum_nil] at this
      exact absurd this (lt_irrefl 0)
    | cons q r' =>
      have hpq : p = q := le_antisymm (h'.head_max h.head_principal h.head_le)
        (h.head_max h'.head_principal h'.head_le)
      rw [← hpq] at h'
      have hs : listSum r = listSum r' := add_right_cancel (h.eq.symm.trans h'.eq)
      have ht := h'.tail
      rw [← hs] at ht
      rw [hpq, ih h.tail ht, ← hpq]

theorem cnf_of_principal {α : Ordinal.{u}} {l : List Ordinal.{u}} (hα : IsPrincipal α)
    (h : CNF α l) : l = [α] := cnf_unique h (cnf_single hα)

theorem cnf_add {y z : Ordinal.{u}} {ly lz : List Ordinal.{u}} (hy : CNF y ly) (hz : CNF z lz) :
    ∃ l, CNF (y + z) l ∧ ∀ p, p ∈ l → p ∈ ly ∨ p ∈ lz := by
  induction ly generalizing y with
  | nil =>
    refine Exists.intro lz (And.intro ?_ (fun p hp => Or.inr hp))
    rw [hy.eq, listSum_nil, zero_add]
    exact hz
  | cons p r ih =>
    cases lz with
    | nil =>
      refine Exists.intro (p :: r) (And.intro ?_ (fun q hq => Or.inl hq))
      rw [hz.eq, listSum_nil, add_zero]
      exact hy
    | cons q rz =>
      cases le_or_lt q p with
      | inl hqp =>
        cases ih hy.tail with
        | intro l0 hl0 =>
          refine Exists.intro (p :: l0) (And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_)
          · intro x hx
            cases List.mem_cons.mp hx with
            | inl e => rw [e]; exact hy.head_principal
            | inr hx => exact hl0.1.principal hx
          · apply List.pairwise_cons.mpr
            apply And.intro _ hl0.1.2.1
            intro x hx
            cases hl0.2 x hx with
            | inl hr => exact hy.head_ge hr
            | inr hq => exact le_trans (hz.mem_le_head hq) hqp
          · rw [listSum_cons, ← hl0.1.eq, hy.eq, listSum_cons, add_assoc]
          · intro x hx
            cases List.mem_cons.mp hx with
            | inl e => rw [e]; exact Or.inl List.mem_cons_self
            | inr hx =>
              cases hl0.2 x hx with
              | inl hr => exact Or.inl (List.mem_cons_of_mem p hr)
              | inr hq => exact Or.inr hq
      | inr hpq =>
        have hyq : y < q := hy.lt_of_head_lt hz.head_principal hpq
        refine Exists.intro (q :: rz) (And.intro ?_ (fun x hx => Or.inr hx))
        have e : y + z = z := by
          rw [hz.eq, listSum_cons, ← add_assoc, hz.head_principal.2.absorb hyq]
        rw [e]
        exact hz

theorem IsPrincipal.add_cases {x y : Ordinal.{u}} (h : IsPrincipal (x + y)) :
    (x + y = x ∧ y = 0) ∨ x + y = y := by
  cases h.add_eq rfl with
  | inl h' => exact Or.inl (And.intro h'.1.symm h'.2)
  | inr h' => exact Or.inr h'.symm

/-! ## Enumerations of classes of ordinals (`EnumDef`, continuity at limits, behaviour below a regular)
and closures.

Copied from the Subsp repository (`Subsp/OCF/Jaeger/Psi.lean`, the generic part before `ISet`). -/

def EnumDef (X : Ordinal.{u} → Prop) (α : Ordinal.{u}) : Prop :=
  ∃ ξ, X ξ ∧ ∀ β, β < α → enum X β < ξ

section Enum

variable {X : Ordinal.{u} → Prop}

theorem EnumDef.of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) : EnumDef X β := by
  cases h with
  | intro ξ hξ =>
    exact Exists.intro ξ (And.intro hξ.1 (fun γ hγ => hξ.2 γ (lt_of_lt_of_le hγ hβ)))

theorem EnumDef.mem {α : Ordinal.{u}} (h : EnumDef X α) : X (enum X α) := (enum_spec X α h).1

theorem EnumDef.lt {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β < α) :
    enum X β < enum X α := (enum_spec X α h).2 β hβ

theorem EnumDef.le_of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) :
    enum X β ≤ enum X α := by
  cases hβ with
  | inl hβ => exact le_of_lt (h.lt hβ)
  | inr hβ => rw [hβ]; exact le_refl _

theorem EnumDef.le_enum {α : Ordinal.{u}} (h : EnumDef X α) : α ≤ enum X α := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    apply le_of_not_lt
    intro hlt
    exact not_lt_of_le (ih _ hlt (h.of_le (le_of_lt hlt))) (h.lt hlt)

theorem EnumDef.lt_iff {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β) :
    enum X β < enum X α ↔ β < α := by
  apply Iff.intro
  · intro h
    apply lt_of_not_le
    intro hle
    exact not_lt_of_le (hβ.le_of_le hle) h
  · exact hα.lt

theorem EnumDef.inj {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β)
    (e : enum X α = enum X β) : α = β := by
  cases lt_total α β with
  | inl h => exact absurd e (ne_of_lt (hβ.lt h))
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact absurd e (ne_of_gt (hα.lt h))

def LimClosed (X : Ordinal.{u} → Prop) : Prop := ∀ ξ, IsLimitPoint X ξ → X ξ

theorem enum_limit (hX : LimClosed X) {l : Ordinal.{u}} (hl : IsLimit l)
    (h : ∀ β, β < l → EnumDef X β) : EnumDef X l ∧ enum X l = supLt l (enum X) := by
  have hlt : ∀ β, β < l → enum X β < supLt l (enum X) := by
    intro β hβ
    exact lt_of_lt_of_le ((h (succ β) (hl.2 β hβ)).lt (lt_succ_self β))
      (le_supLt l (enum X) (hl.2 β hβ))
  have hXs : X (supLt l (enum X)) := by
    apply hX
    apply And.intro (lt_of_le_of_lt (zero_le _) (hlt 0 hl.1))
    intro η hη
    cases (lt_supLt_iff l (enum X) η).mp hη with
    | intro β hβ => exact Exists.intro (enum X β) (And.intro (h β hβ.1).mem
        (And.intro hβ.2 (hlt β hβ.1)))
  have hdef : EnumDef X l := Exists.intro _ (And.intro hXs hlt)
  refine And.intro hdef (le_antisymm (enum_le hXs hlt) ?_)
  exact (supLt_le_iff _ _ _).mpr (fun β hβ => le_of_lt (hdef.lt hβ))

theorem enum_below_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) :
    ∀ α, α < θ → EnumDef X α ∧ enum X α < θ := by
  intro α
  induction α using lt_wellFounded.induction with
  | h α ih =>
    intro hα
    have hs : supLt α (enum X) < θ :=
      hθ.supLt_lt hα (fun β hβ => (ih β hβ (lt_trans β α θ hβ hα)).2)
    cases hunb _ hs with
    | intro ξ hξ =>
      have hbelow : ∀ β, β < α → enum X β < ξ :=
        fun β hβ => lt_of_le_of_lt (le_supLt α (enum X) hβ) hξ.2.1
      exact And.intro (Exists.intro ξ (And.intro hξ.1 hbelow))
        (lt_of_le_of_lt (enum_le hξ.1 hbelow) hξ.2.2)

theorem enum_fixed_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) (hXθ : X θ) :
    EnumDef X θ ∧ enum X θ = θ := by
  have hb := enum_below_regular hθ hunb
  have hdef : EnumDef X θ := Exists.intro θ (And.intro hXθ (fun β hβ => (hb β hβ).2))
  exact And.intro hdef (le_antisymm (enum_le hXθ (fun β hβ => (hb β hβ).2)) hdef.le_enum)

end Enum

theorem subset_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}} (h : A ξ) : closure A ξ :=
  (closure_iff A ξ).mpr (Or.inl h)

theorem isLimitPoint_of_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}}
    (h : IsLimitPoint (closure A) ξ) : IsLimitPoint A ξ := by
  apply And.intro h.1
  intro η hη
  cases h.2 η hη with
  | intro b hb =>
    cases (closure_iff A b).mp hb.1 with
    | inl hA => exact Exists.intro b (And.intro hA hb.2)
    | inr hlp =>
      cases hlp.2 η hb.2.1 with
      | intro a ha => exact Exists.intro a (And.intro ha.1 (And.intro ha.2.1
          (lt_trans a b ξ ha.2.2 hb.2.2)))

theorem closure_limClosed (A : Ordinal.{u} → Prop) : LimClosed (closure A) :=
  fun ξ h => (closure_iff A ξ).mpr (Or.inr (isLimitPoint_of_closure h))

/-! ## 閉非有界集合と定常集合。

`κ` を非可算正則基数（`R κ`）とし、`κ` 未満の順序数のクラスについて

* `Unbounded κ X`：`X` は `κ` で非有界
* `ClosedBelow κ X`：`κ` 未満の `X` の極限点は `X` に入る
* `Club κ X`：その両方
* `Stationary κ S`：全ての `Club κ X` と交わる

を定める。主な結果は、二つの閉非有界集合の共通部分が閉非有界であること（`Club.inter`）と、
極限順序数・`η` より大きい順序数が閉非有界であること。 -/

def Unbounded (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∀ η, η < κ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < κ

/-- A function from a regular ordinal into a smaller ordinal has an unbounded
fiber.  This form of the regularity argument will be used to thin sequences
of first-difference coordinates. -/
theorem exists_unbounded_fiber {κ δ : Ordinal.{u}} (hκ : IsRegular κ)
    (hδ : δ < κ) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, x < κ → f x < δ) :
    ∃ y, y < δ ∧ Unbounded κ (fun x => x < κ ∧ f x = y) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ y, y < δ → ¬ Unbounded κ (fun x => x < κ ∧ f x = y) := by
    intro y hy hU
    exact hnone ⟨y, hy, hU⟩
  have hbound : ∀ y, y < δ →
      ∃ b, b < κ ∧ ∀ x, x < κ → f x = y → x ≤ b := by
    intro y hy
    apply Classical.byContradiction
    intro hn
    have hU : Unbounded κ (fun x => x < κ ∧ f x = y) := by
      intro b hb
      have hnot : ¬ (∀ x, x < κ → f x = y → x ≤ b) := by
        intro hle
        exact hn ⟨b, hb, hle⟩
      have hex : ∃ x, x < κ ∧ f x = y ∧ ¬ x ≤ b := by
        apply Classical.byContradiction
        intro h
        apply hnot
        intro x hx hxy
        by_cases hxb : x ≤ b
        · exact hxb
        · exact False.elim (h ⟨x, hx, hxy, hxb⟩)
      obtain ⟨x, hx, hxy, hxb⟩ := hex
      exact ⟨x, ⟨hx, hxy⟩, lt_of_not_le hxb, hx⟩
    exact hno y hy hU
  let bound : Ordinal.{u} → Ordinal.{u} := fun y =>
    if hy : y < δ then Classical.choose (hbound y hy) else 0
  have hbound_lt : ∀ y, bound y < κ := by
    intro y
    by_cases hy : y < δ
    · have heq : bound y = Classical.choose (hbound y hy) := dite_eq_left hy
      rw [heq]
      exact (Classical.choose_spec (hbound y hy)).1
    · have heq : bound y = 0 := dite_eq_right hy
      rw [heq]
      exact hκ.pos
  have hbound_spec : ∀ y, y < δ → ∀ x, x < κ → f x = y → x ≤ bound y := by
    intro y hy x hx hxy
    have heq : bound y = Classical.choose (hbound y hy) := dite_eq_left hy
    rw [heq]
    exact (Classical.choose_spec (hbound y hy)).2 x hx hxy
  let s := supLt δ bound
  have hs : s < κ := hκ.supLt_lt hδ (fun y _ => hbound_lt y)
  have hsucc : succ s < κ := hκ.1.2 s hs
  have hfs : f (succ s) < δ := hf (succ s) hsucc
  have hle₁ : succ s ≤ bound (f (succ s)) := hbound_spec _ hfs _ hsucc rfl
  have hle₂ : bound (f (succ s)) ≤ s := le_supLt δ bound hfs
  have hle : succ s ≤ s := le_trans hle₁ hle₂
  exact lt_irrefl s (lt_of_lt_of_le (lt_succ_self s) hle)

def ClosedBelow (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∀ l, l < κ → IsLimitPoint X l → X l

def Club (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop := Unbounded κ X ∧ ClosedBelow κ X

def Stationary (κ : Ordinal.{u}) (S : Ordinal.{u} → Prop) : Prop :=
  ∀ X, Club κ X → ∃ ξ, ξ < κ ∧ X ξ ∧ S ξ

/-! ### 正則基数の下の ω 列の上限 -/

/-- 狭義増加の ω 列の上限 -/
def omegaSup (s : Nat → Ordinal.{u}) : Ordinal.{u} := supLt omega (fun ζ => s (natOf ζ))

theorem lt_omegaSup {s : Nat → Ordinal.{u}} (hs : ∀ n, s n < s (n + 1)) (n : Nat) :
    s n < omegaSup s := by
  apply (lt_supLt_iff _ _ _).mpr
  refine Exists.intro (ordNat (n + 1)) (And.intro (ordNat_lt_omega _) ?_)
  rw [natOf_ordNat]
  exact hs n

theorem lt_omegaSup_iff {s : Nat → Ordinal.{u}} (ζ : Ordinal.{u}) :
    ζ < omegaSup s ↔ ∃ n, ζ < s n := by
  apply Iff.intro
  · intro h
    cases (lt_supLt_iff _ _ _).mp h with
    | intro ξ hξ => exact Exists.intro (natOf ξ) hξ.2
  · intro h
    cases h with
    | intro n hn =>
      apply (lt_supLt_iff _ _ _).mpr
      refine Exists.intro (ordNat n) (And.intro (ordNat_lt_omega _) ?_)
      rw [natOf_ordNat]
      exact hn

theorem omegaSup_lt {κ : Ordinal.{u}} (hκ : R κ) {s : Nat → Ordinal.{u}} (h : ∀ n, s n < κ) :
    omegaSup s < κ :=
  hκ.2.supLt_lt hκ.1 (fun ξ _ => h (natOf ξ))

/-- 狭義増加の ω 列の上限は極限順序数で、列の各項の極限点 -/
theorem omegaSup_isLimitPoint {s : Nat → Ordinal.{u}} (hs : ∀ n, s n < s (n + 1))
    {X : Ordinal.{u} → Prop} (hX : ∀ n, X (s (n + 1))) : IsLimitPoint X (omegaSup s) := by
  apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
  intro η hη
  cases (lt_omegaSup_iff η).mp hη with
  | intro n hn =>
    exact Exists.intro (s (n + 1)) (And.intro (hX n)
      (And.intro (lt_trans _ _ _ hn (hs n)) (lt_omegaSup hs (n + 1))))

/-! ### 閉非有界集合 -/

/-- `X` が非有界なとき、`ζ` より大きい `X` の元を一つ選ぶ（`ζ ≥ κ` なら `0`） -/
def nextAbove (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) (h : Unbounded κ X) (ζ : Ordinal.{u}) :
    Ordinal.{u} :=
  open Classical in
  if hζ : ζ < κ then Classical.choose (h ζ hζ) else 0

theorem nextAbove_spec {κ : Ordinal.{u}} {X : Ordinal.{u} → Prop} (h : Unbounded κ X)
    {ζ : Ordinal.{u}} (hζ : ζ < κ) :
    X (nextAbove κ X h ζ) ∧ ζ < nextAbove κ X h ζ ∧ nextAbove κ X h ζ < κ := by
  unfold nextAbove
  rw [dite_eq_left hζ]
  exact Classical.choose_spec (h ζ hζ)

/-- 二つの非有界集合の元を交互にとる列 -/
def alternate (κ : Ordinal.{u}) (X Y : Ordinal.{u} → Prop) (hX : Unbounded κ X)
    (hY : Unbounded κ Y) (η : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => η
  | n + 1 => nextAbove κ Y hY (nextAbove κ X hX (alternate κ X Y hX hY η n))

theorem alternate_spec {κ : Ordinal.{u}} {X Y : Ordinal.{u} → Prop} (hX : Unbounded κ X)
    (hY : Unbounded κ Y) {η : Ordinal.{u}} (hη : η < κ) (n : Nat) :
    alternate κ X Y hX hY η n < κ ∧
      X (nextAbove κ X hX (alternate κ X Y hX hY η n)) ∧
      alternate κ X Y hX hY η n < nextAbove κ X hX (alternate κ X Y hX hY η n) ∧
      nextAbove κ X hX (alternate κ X Y hX hY η n) < alternate κ X Y hX hY η (n + 1) ∧
      Y (alternate κ X Y hX hY η (n + 1)) ∧ alternate κ X Y hX hY η (n + 1) < κ := by
  induction n with
  | zero =>
    have h1 := nextAbove_spec hX hη
    have h2 := nextAbove_spec hY h1.2.2
    exact ⟨hη, h1.1, h1.2.1, h2.2.1, h2.1, h2.2.2⟩
  | succ n ih =>
    have h1 := nextAbove_spec hX ih.2.2.2.2.2
    have h2 := nextAbove_spec hY h1.2.2
    exact ⟨ih.2.2.2.2.2, h1.1, h1.2.1, h2.2.1, h2.1, h2.2.2⟩

theorem Club.inter {κ : Ordinal.{u}} (hκ : R κ) {X Y : Ordinal.{u} → Prop} (hX : Club κ X)
    (hY : Club κ Y) : Club κ (fun ξ => X ξ ∧ Y ξ) := by
  apply And.intro
  · intro η hη
    let s := alternate κ X Y hX.1 hY.1 η
    have hsp := alternate_spec hX.1 hY.1 hη
    have hs : ∀ n, s n < s (n + 1) := fun n =>
      lt_trans _ _ _ (hsp n).2.2.1 (hsp n).2.2.2.1
    have hlt : omegaSup s < κ := omegaSup_lt hκ (fun n => (hsp n).1)
    have hYl : IsLimitPoint Y (omegaSup s) :=
      omegaSup_isLimitPoint hs (fun n => (hsp n).2.2.2.2.1)
    have hXl : IsLimitPoint X (omegaSup s) := by
      apply And.intro hYl.1
      intro ζ hζ
      cases (lt_omegaSup_iff ζ).mp hζ with
      | intro n hn =>
        exact Exists.intro _ (And.intro (hsp n).2.1
          (And.intro (lt_trans _ _ _ hn (hsp n).2.2.1)
            (lt_trans _ _ _ (hsp n).2.2.2.1 (lt_omegaSup hs (n + 1)))))
    exact Exists.intro (omegaSup s) (And.intro (And.intro (hX.2 _ hlt hXl) (hY.2 _ hlt hYl))
      (And.intro (lt_omegaSup hs 0) hlt))
  · intro l hl hlp
    apply And.intro
    · apply hX.2 l hl
      apply And.intro hlp.1
      intro η hη
      cases hlp.2 η hη with
      | intro β hβ => exact Exists.intro β (And.intro hβ.1.1 hβ.2)
    · apply hY.2 l hl
      apply And.intro hlp.1
      intro η hη
      cases hlp.2 η hη with
      | intro β hβ => exact Exists.intro β (And.intro hβ.1.2 hβ.2)

/-- `η < κ` なら `η` より大きい順序数は閉非有界 -/
theorem club_gt {κ : Ordinal.{u}} (hκ : R κ) {η : Ordinal.{u}} (hηκ : η < κ) :
    Club κ (fun ξ => η < ξ) := by
  apply And.intro
  · intro ζ hζ
    cases lt_or_le ζ η with
    | inl h =>
      exact Exists.intro (succ η) (And.intro (lt_succ_self η)
        (And.intro (lt_trans _ _ _ h (lt_succ_self η)) (hκ.2.1.succ_lt hηκ)))
    | inr h =>
      exact Exists.intro (succ ζ) (And.intro (lt_of_le_of_lt h (lt_succ_self ζ))
        (And.intro (lt_succ_self ζ) (hκ.2.1.succ_lt hζ)))
  · intro l _ hlp
    cases hlp.2 0 hlp.1 with
    | intro β hβ => exact lt_trans _ _ _ hβ.1 hβ.2.2

/-- 極限順序数は閉非有界 -/
theorem club_isLimit {κ : Ordinal.{u}} (hκ : R κ) : Club κ IsLimit := by
  apply And.intro
  · intro η hη
    let s : Nat → Ordinal.{u} := fun n => η + ordNat n
    have hs : ∀ n, s n < s (n + 1) := fun n => by
      show η + ordNat n < η + ordNat (n + 1)
      exact (add_lt_add_iff_right η).mpr (ordNat_lt (Nat.lt_succ_self n))
    have hsκ : ∀ n, s n < κ := fun n => hκ.2.add_lt hη (lt_trans _ _ _ (ordNat_lt_omega n) hκ.1)
    refine Exists.intro (omegaSup s) (And.intro ?_ (And.intro ?_ (omegaSup_lt hκ hsκ)))
    · apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn =>
        exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    · have h0 : s 0 = η := add_zero η
      rw [← h0]
      exact lt_omegaSup hs 0
  · intro l _ hlp
    apply And.intro hlp.1
    intro β hβ
    cases hlp.2 β hβ with
    | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2

theorem Stationary.mono {κ : Ordinal.{u}} {S T : Ordinal.{u} → Prop} (h : Stationary κ S)
    (hST : ∀ ξ, ξ < κ → S ξ → T ξ) : Stationary κ T := by
  intro X hX
  cases h X hX with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.1 (And.intro hξ.2.1 (hST ξ hξ.1 hξ.2.2)))

/-- 定常集合は非有界 -/
theorem Stationary.unbounded {κ : Ordinal.{u}} (hκ : R κ) {S : Ordinal.{u} → Prop}
    (h : Stationary κ S) : Unbounded κ S := by
  intro η hη
  cases h _ (club_gt hκ hη) with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.2.2 (And.intro hξ.2.1 hξ.1))

/-- 極限順序数全体は定常 -/
theorem stationary_isLimit {κ : Ordinal.{u}} (hκ : R κ) : Stationary κ IsLimit := by
  intro X hX
  cases (Club.inter hκ hX (club_isLimit hκ)).1 0 hκ.2.pos with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.2.2 (And.intro hξ.1.1 hξ.1.2))

/-! ### 二つの順序数の大きい方 -/

/-- 大きい方 -/
def omax (a b : Ordinal.{u}) : Ordinal.{u} :=
  open Classical in
  if a < b then b else a

theorem le_omax_left (a b : Ordinal.{u}) : a ≤ omax a b := by
  unfold omax
  split
  · exact Or.inl ‹_›
  · exact le_refl a

theorem le_omax_right (a b : Ordinal.{u}) : b ≤ omax a b := by
  unfold omax
  split
  · exact le_refl b
  · exact le_of_not_lt ‹_›

theorem omax_lt {a b c : Ordinal.{u}} (ha : a < c) (hb : b < c) : omax a b < c := by
  unfold omax
  split
  · exact hb
  · exact ha

end
end Rathjen
end OCF
