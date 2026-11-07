/-! 基本列の公理。

`Cof` は共終数の型：`0`、後者、`ω`、正則項 `σ`（添字は `σ` 未満の元）。`big` の場合の公理は、基本列が元の
項より小さいこと（`big_lt`）、添字について狭義単調であること（`big_mono`）、共終であること（`big_cof`）。
`omega` の場合は、それに加えて Bachmann 性（`omega_bachmann`）を課す。 -/

class Well_Order (A : Type) [LT A] where
  lt_trans : ∀ a b c : A, a < b → b < c → a < c
  lt_total : ∀ a b : A, a < b ∨ b < a ∨ a = b
  lt_wf : WellFounded (fun a b : A => a < b)

instance (A : Type) [LT A] [Well_Order A] : LE A where
  le a b := a < b ∨ a = b

instance (A : Type) [DecidableEq A] [LT A] [DecidableLT A] [Well_Order A] : DecidableLE A :=
  fun a b => inferInstanceAs (Decidable (a < b ∨ a = b))

/-- 共終数の型：`0`、後者、`ω`、正則項 `σ`（添字は `σ` 未満） -/
inductive Cof (A : Type) where
  | zero
  | one
  | omega
  | big (σ : A)

/-- 基本列が満たす性質 -/
class FS (A : Type) [DecidableEq A] [LT A] [DecidableLT A] [Well_Order A] where
  fund : A → A → A
  dom : A → Cof A
  Z : A
  ofNat : Nat → A

  ofNat_zero : ofNat 0 = Z
  ofNat_dom : ∀ n, dom (ofNat (n + 1)) = .one
  ofNat_fund : ∀ n m, fund (ofNat (n + 1)) m = ofNat n

  zero_dom : dom Z = .zero
  zero_unique : ∀ a, dom a = .zero → a = Z
  zero_fund : ∀ n, fund Z n = Z

  succ_md : ∀ a n, dom a = .one → fund a n < a
  succ_cof : ∀ a n x, dom a = .one → x < a → x ≤ fund a n

  omega_lt : ∀ a n, dom a = .omega → fund a (ofNat n) < a
  omega_mono : ∀ a n, dom a = .omega → fund a (ofNat n) < fund a (ofNat (n + 1))
  omega_bachmann : ∀ a b n, dom a = .omega → fund a (ofNat n) < b → b < a →
    fund a (ofNat n) ≤ fund b (ofNat 0)
  omega_cof : ∀ a x, dom a = .omega → x < a → ∃ n, x ≤ fund a (ofNat n)

  big_lt : ∀ a σ ξ, dom a = .big σ → ξ < σ → fund a ξ < a
  big_mono : ∀ a σ ξ η, dom a = .big σ → ξ < η → η < σ → fund a ξ < fund a η
  big_cof : ∀ a σ x, dom a = .big σ → x < a → ∃ ξ, ξ < σ ∧ x ≤ fund a ξ
