import Mahlo.Ordinal

/-! 基数の設定と、崩壊関数 `Ξ`・`Ψ` の定義。

* `M_1 < M_2 < ⋯` は弱 Mahlo 基数の増加列（`Setting`）。`K 0 = 0`、`K (n+1) = M_{n+1}`、`Λ = sup K_n`。
  弱 Mahlo 基数は「非可算正則で、正則基数全体が定常」（`WeaklyMahlo`）。
* `Ω_x = ℵ_{1+x}`：非可算基数全体の数え上げ（`Ω_0 = ℵ_1`）。
* 段 `α` について再帰的に、
  - `C(α, β)`：`β ∪ {K_m}` を `+`、`Ω`（引数 `< Λ`）、`Ξ_m(ξ)`（`ξ < α`）、
    `Ψ_π(δ)`（`δ < α`、`π` 正則、`Ψ_π(δ) < π` で `δ ∈ C(δ, Ψ_π(δ))`）で閉じたもの。
  - `M^α = {ρ ∈ Reg : C(α, ρ) ∩ K(ρ) ⊆ ρ ∧ α ∈ C(α, ρ)}`（定常性の条件は無い）。
  - `Ξ_m(α) = min((M^α ∩ (K_{m-1}, K_m)) ∪ {K_m})`（`M_m` への Mahlo 崩壊）。
  - `Ψ_π(α) = min({η < π : Base_π(η) ∧ C(α, η) ∩ π ⊆ η} ∪ {π})`（Buchholz 型の崩壊）。
    底の条件 `Base_π(η)` は崩壊先 `π` 自身だけで決まる：
    `Base_{Ω_0}(η) ⟺ 0 < η`、`Base_{Ω_{ζ+1}}(η) ⟺ Ω_ζ < η`、
    `Base_{Ξ_m(δ)}(η) ⟺ K_{m-1} < η ∧ δ ∈ C(δ, η)`（`δ < α` のときだけ有効）。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen

noncomputable section

/-! ### 閉包の数え上げ -/

theorem enum_closure_zero_mem {A : Ordinal.{u} → Prop} (h : EnumDef (closure A) 0) :
    A (enum (closure A) 0) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 0 hlp.1 with
    | intro a ha =>
      have := enum_le (X := closure A) (α := 0) (subset_closure ha.1)
        (fun β hβ => absurd hβ (not_lt_zero β))
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

theorem enum_closure_succ_mem {A : Ordinal.{u} → Prop} {β : Ordinal.{u}}
    (h : EnumDef (closure A) (succ β)) : A (enum (closure A) (succ β)) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 _ (h.lt (lt_succ_self β)) with
    | intro a ha =>
      have hβ : EnumDef (closure A) β := h.of_le (le_of_lt (lt_succ_self β))
      have := enum_le (X := closure A) (α := succ β) (subset_closure ha.1)
        (fun γ hγ => lt_of_le_of_lt (hβ.le_of_le (le_of_lt_succ hγ)) ha.2.1)
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

/-- 非可算正則基数の閉包の元は加法的主数 -/
theorem principal_of_closure_R {ξ : Ordinal.{u}} (h : closure R ξ) : IsPrincipal ξ := by
  cases (closure_iff R ξ).mp h with
  | inl hR => exact hR.2.isPrincipal
  | inr hlp =>
    refine And.intro (ne_of_gt hlp.1) (addPrincipal_of_limit ?_)
    intro η hη
    cases hlp.2 η hη with
    | intro ρ hρ =>
      exact Exists.intro ρ (And.intro hρ.1.2.addPrincipal (And.intro hρ.2.1 (Or.inl hρ.2.2)))

/-- 正則基数 `κ` 未満の小さい集合は `κ` 未満で抑えられる -/
theorem Small.bounded {κ : Ordinal.{u}} (hκ : IsRegular κ) {A : Ordinal.{u} → Prop}
    (h : Small κ A) (hA : ∀ x, A x → x < κ) : ∃ γ, γ < κ ∧ ∀ x, A x → x < γ := by
  classical
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      let pre : Ordinal.{u} → Ordinal.{u} := fun ζ =>
        if h : ∃ x, A x ∧ f x = ζ then Classical.choose h else 0
      have hpre : ∀ x, A x → pre (f x) = x := by
        intro x hx
        have h : ∃ y, A y ∧ f y = f x := Exists.intro x (And.intro hx rfl)
        have e : pre (f x) = Classical.choose h := dite_eq_left h
        rw [e]
        have hs := Classical.choose_spec h
        exact hf.2 _ _ hs.1 hx hs.2
      have hpreκ : ∀ ζ, pre ζ < κ := by
        intro ζ
        by_cases h : ∃ x, A x ∧ f x = ζ
        · have e : pre ζ = Classical.choose h := dite_eq_left h
          rw [e]
          exact hA _ (Classical.choose_spec h).1
        · have e : pre ζ = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      refine Exists.intro (supLt β (fun ζ => succ (pre ζ)))
        (And.intro (hκ.supLt_lt hβ.1 (fun ζ _ => hκ.1.succ_lt (hpreκ ζ))) ?_)
      intro x hx
      apply (lt_supLt_iff _ _ _).mpr
      refine Exists.intro (f x) (And.intro (hf.1 x hx) ?_)
      show x < succ (pre (f x))
      rw [hpre x hx]
      exact lt_succ_self x

/-! ### 弱 Mahlo 基数の列 -/

/-- 弱 Mahlo 基数：非可算正則で、その下の非可算正則基数全体が定常 -/
def WeaklyMahlo (κ : Ordinal.{u}) : Prop := R κ ∧ Stationary κ R

/-- 弱 Mahlo 基数の増加列 `M_1 < M_2 < ⋯`（`Kseq n` が `M_{n+1}`） -/
class Setting : Type (u + 1) where
  Kseq : Nat → Ordinal.{u}
  Kseq_mahlo : ∀ n, WeaklyMahlo (Kseq n)
  Kseq_lt : ∀ n, Kseq n < Kseq (n + 1)

variable [Setting.{u}]

/-- `K_0 = 0`、`K_{n+1} = M_{n+1}` -/
def K : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => Setting.Kseq n

def Λ : Ordinal.{u} := sup (fun n : ULift.{u} Nat => K n.down)

theorem K_zero : K.{u} 0 = 0 := rfl

theorem mahlo_K {n : Nat} (h : 1 ≤ n) : WeaklyMahlo (K.{u} n) := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n => exact Setting.Kseq_mahlo n

theorem R_K {n : Nat} (h : 1 ≤ n) : R (K.{u} n) := (mahlo_K h).1

theorem K_lt_K_succ (n : Nat) : K.{u} n < K (n + 1) := by
  cases n with
  | zero =>
    exact lt_of_le_of_lt (zero_le _) (lt_trans _ _ _ zero_lt_omega (Setting.Kseq_mahlo 0).1.1)
  | succ n => exact Setting.Kseq_lt n

theorem K_lt {m n : Nat} (h : m < n) : K.{u} m < K n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl h' => exact lt_trans _ _ _ (ih h') (K_lt_K_succ n)
    | inr h' => rw [h']; exact K_lt_K_succ n

theorem K_le {m n : Nat} (h : m ≤ n) : K.{u} m ≤ K n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h' => exact Or.inl (K_lt h')
  | inr h' => rw [h']; exact le_refl _

theorem K_lt_iff {m n : Nat} : K.{u} m < K n ↔ m < n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge m n with
    | inl h' => exact h'
    | inr h' => exact absurd h (not_lt_of_le (K_le h'))
  · exact K_lt

theorem K_le_iff {m n : Nat} : K.{u} m ≤ K n ↔ m ≤ n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge n m with
    | inl h' => exact absurd (K_lt h') (not_lt_of_le h)
    | inr h' => exact h'
  · exact K_le

theorem K_inj {m n : Nat} (h : K.{u} m = K n) : m = n := by
  cases Nat.lt_trichotomy m n with
  | inl h' => exact absurd h (ne_of_lt (K_lt h'))
  | inr h' =>
    cases h' with
    | inl h' => exact h'
    | inr h' => exact absurd h (ne_of_gt (K_lt h'))

theorem K_le_Λ (n : Nat) : K.{u} n ≤ Λ :=
  le_sup (fun k : ULift.{u} Nat => K k.down) (ULift.up n)

theorem K_lt_Λ (n : Nat) : K.{u} n < Λ :=
  lt_of_lt_of_le (K_lt_K_succ n) (K_le_Λ (n + 1))

theorem lt_Λ_iff (α : Ordinal.{u}) : α < Λ ↔ ∃ n, α < K n := by
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ α).mp h with
    | intro n hn => exact Exists.intro n.down hn
  · intro h
    cases h with
    | intro n hn => exact lt_trans _ _ _ hn (K_lt_Λ n)

theorem Λ_pos : (0 : Ordinal.{u}) < Λ := K_lt_Λ 0

/-- `K_n`（`n ≥ 1`）未満の正則基数は非有界 -/
theorem K_inacc {n : Nat} (h : 1 ≤ n) (η : Ordinal.{u}) (hη : η < K n) :
    ∃ ρ, R ρ ∧ η < ρ ∧ ρ < K n := by
  cases (mahlo_K h).2 _ (club_gt (R_K h) hη) with
  | intro ρ hρ => exact ⟨ρ, hρ.2.2, hρ.2.1, hρ.1⟩

theorem isLimit_Λ : IsLimit (Λ : Ordinal.{u}) := by
  apply And.intro Λ_pos
  intro β hβ
  cases (lt_Λ_iff β).mp hβ with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero β)
    | succ n =>
      exact lt_trans _ _ _ ((R_K (Nat.succ_le_succ (Nat.zero_le n))).2.1.succ_lt hn) (K_lt_Λ _)

theorem omega_lt_K {n : Nat} (h : 1 ≤ n) : omega < K.{u} n := (R_K h).1

/-! ### `Ω_x = ℵ_{1+x}` -/

/-- `Ω`：非可算基数全体（非可算正則基数の閉包）の数え上げ -/
def Om : Ordinal.{u} → Ordinal.{u} := enum (closure R)

theorem cardSet_unbounded_K {n : Nat} (h : 1 ≤ n) :
    ∀ η, η < K.{u} n → ∃ ξ, closure R ξ ∧ η < ξ ∧ ξ < K n := by
  intro η hη
  cases K_inacc h η hη with
  | intro ρ hρ => exact Exists.intro ρ (And.intro (subset_closure hρ.1) hρ.2)

theorem Om_def_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) :
    EnumDef (closure R) α ∧ Om α < K n :=
  enum_below_regular (R_K h).2 (cardSet_unbounded_K h) α hα

theorem Om_def {α : Ordinal.{u}} (hα : α < Λ) : EnumDef (closure R) α := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero α)
    | succ n => exact (Om_def_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hn).1

theorem Om_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) : Om α < K n :=
  (Om_def_lt_K h hα).2

/-- `x < K_n` なら `Ω_x < K_n`（`n = 0` は空虚） -/
theorem Om_lt_K' {n : Nat} {α : Ordinal.{u}} (hα : α < K n) : Om α < K n := by
  cases n with
  | zero => exact absurd hα (not_lt_zero α)
  | succ n => exact Om_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hα

theorem Om_lt_Λ {α : Ordinal.{u}} (hα : α < Λ) : Om α < Λ := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn => exact lt_trans _ _ _ (Om_lt_K' hn) (K_lt_Λ n)

theorem Om_K {n : Nat} (h : 1 ≤ n) : Om (K.{u} n) = K n :=
  (enum_fixed_regular (R_K h).2 (cardSet_unbounded_K h) (subset_closure (R_K h))).2

theorem Om_lt_Om {α β : Ordinal.{u}} (hαβ : α < β) (hβ : β < Λ) : Om α < Om β :=
  (Om_def hβ).lt hαβ

theorem Om_lt_Om_iff {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) : Om α < Om β ↔ α < β :=
  (Om_def hβ).lt_iff (Om_def hα)

theorem Om_le_Om {α β : Ordinal.{u}} (hαβ : α ≤ β) (hβ : β < Λ) : Om α ≤ Om β := by
  cases hαβ with
  | inl h => exact Or.inl (Om_lt_Om h hβ)
  | inr h => rw [h]; exact le_refl _

theorem Om_inj {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) (h : Om α = Om β) : α = β :=
  (Om_def hα).inj (Om_def hβ) h

theorem le_Om {α : Ordinal.{u}} (hα : α < Λ) : α ≤ Om α := (Om_def hα).le_enum

theorem cardSet_Om {α : Ordinal.{u}} (hα : α < Λ) : closure R (Om α) := (Om_def hα).mem

theorem Om_principal {α : Ordinal.{u}} (hα : α < Λ) : IsPrincipal (Om α) :=
  principal_of_closure_R (cardSet_Om hα)

theorem Om_pos {α : Ordinal.{u}} (hα : α < Λ) : 0 < Om α := (Om_principal hα).pos

/-- `Ω_0` は正則 -/
theorem Om_zero_R : R (Om (0 : Ordinal.{u})) :=
  enum_closure_zero_mem (Om_def Λ_pos)

/-- `Ω_{β+1}` は正則 -/
theorem Om_succ_R {β : Ordinal.{u}} (hβ : succ β < Λ) : R (Om (succ β)) :=
  enum_closure_succ_mem (Om_def hβ)

/-- `Ω` は極限で連続 -/
theorem Om_limit {l : Ordinal.{u}} (hl : IsLimit l) (hlΛ : l < Λ) : Om l = supLt l Om :=
  (enum_limit (closure_limClosed R) hl (fun _ hβ => Om_def (lt_trans _ _ _ hβ hlΛ))).2

/-- 非可算基数は `Ω` の値 -/
theorem Om_surj {ξ : Ordinal.{u}} (hξ : closure R ξ) (hξΛ : ξ < Λ) : ∃ β, β < Λ ∧ Om β = ξ := by
  have hdef := Om_def hξΛ
  have hle : ξ ≤ Om ξ := le_Om hξΛ
  cases Ordinal.exists_min (fun β => ξ ≤ Om β) (Exists.intro ξ hle) with
  | intro β hβ =>
    have hβξ : β ≤ ξ := le_of_not_lt (fun hlt => hβ.2 ξ hlt hle)
    have hβΛ : β < Λ := lt_of_le_of_lt hβξ hξΛ
    refine Exists.intro β (And.intro hβΛ (le_antisymm ?_ hβ.1))
    exact enum_le hξ (fun γ hγ => lt_of_not_le (hβ.2 γ hγ))

/-- 正則基数 `ρ < Λ` は `Ω_0` 以上 -/
theorem Om_zero_le_of_R {ρ : Ordinal.{u}} (hρ : R ρ) : Om 0 ≤ ρ :=
  enum_le (subset_closure hρ) (fun β hβ => absurd hβ (not_lt_zero β))

theorem Om_zero_lt_K {n : Nat} (h : 1 ≤ n) : Om (0 : Ordinal.{u}) < K n :=
  Om_lt_K h (R_K h).2.pos

theorem one_lt_Om {α : Ordinal.{u}} (hα : α < Λ) : succ 0 < Om α := by
  have h0 := Om_zero_le_of_R Om_zero_R
  apply lt_of_lt_of_le _ (Om_le_Om (zero_le α) hα)
  exact lt_trans _ _ _ (ordNat_lt_omega 1) Om_zero_R.1

/-! ## 段ごとの定義 -/

/-- `Reg`：`Λ` 未満の非可算正則基数で、どの `K_n` とも等しくないもの -/
def IsReg (π : Ordinal.{u}) : Prop := R π ∧ π < Λ ∧ ∀ n, π ≠ K n

/-- `K(π)`：`π` より大きい最小の `K_n` -/
def Kabove (π : Ordinal.{u}) : Ordinal.{u} := least (fun κ => (∃ n, κ = K n) ∧ π < κ)

/-- `Ξ_m` の引数の上限 `M_m^+ = Ω_{M_m + 1}`（元論文の `χ` の添字 `< ε_{M+1}` にあたる） -/
def capK (m : Nat) : Ordinal.{u} := Om (K m + succ 0)

/-- 段 `α` で定まるもの -/
structure Stage : Type (u + 1) where
  /-- `C β x`：`x ∈ C(α, β)` -/
  C : Ordinal.{u} → Ordinal.{u} → Prop
  /-- `M^α` -/
  M : Ordinal.{u} → Prop
  /-- `Ξ_m(α)` -/
  Xi : Nat → Ordinal.{u}
  /-- `Ψ_π(α)` -/
  Psi : Ordinal.{u} → Ordinal.{u}

/-- `C(α, β)` の段階 `n` の元 -/
inductive StageC (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (β : Ordinal.{u}) : Nat → Ordinal.{u} → Prop where
  | lt (n : Nat) (γ : Ordinal.{u}) (h : γ < β) : StageC α prev β n γ
  | kc (n m : Nat) : StageC α prev β n (K m)
  | add (n : Nat) (x y : Ordinal.{u}) (hx : StageC α prev β n x) (hy : StageC α prev β n y) :
      StageC α prev β (n + 1) (x + y)
  | om (n : Nat) (x : Ordinal.{u}) (hΛ : x < Λ) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) (Om x)
  | xi (n m : Nat) (x : Ordinal.{u}) (hα : x < α) (hcap : x ≤ capK m) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) ((prev x hα).Xi m)
  | psi (n : Nat) (π δ : Ordinal.{u}) (hα : δ < α) (hπ : IsReg π)
      (hlt : (prev δ hα).Psi π < π) (hnorm : (prev δ hα).C ((prev δ hα).Psi π) δ)
      (hπC : StageC α prev β n π) (hδ : StageC α prev β n δ) :
      StageC α prev β (n + 1) ((prev δ hα).Psi π)

/-- 段 `α` での崩壊先 `π` の底の条件 -/
def BaseAt (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (π η : Ordinal.{u}) : Prop :=
  (π = Om 0 ∧ 0 < η) ∨ (∃ ζ, succ ζ < Λ ∧ π = Om (succ ζ) ∧ Om ζ < η) ∨
    (∃ m δ, ∃ h : δ < α, δ ≤ capK m ∧ π = (prev δ h).Xi m ∧ π < K m ∧ K (m - 1) < η ∧
      (prev δ h).C η δ)

def makeStage (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u}) : Stage.{u} :=
  let C : Ordinal.{u} → Ordinal.{u} → Prop := fun β x => ∃ n, StageC α prev β n x
  let M : Ordinal.{u} → Prop := fun ρ =>
    IsReg ρ ∧ (∀ x, C ρ x → x < Kabove ρ → x < ρ) ∧ C ρ α
  { C := C
    M := M
    Xi := fun m => least (fun π => (M π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    Psi := fun π => least (fun η =>
      (BaseAt α prev π η ∧ η < π ∧ ∀ x, C η x → x < π → x < η) ∨ η = π) }

def stages : Ordinal.{u} → Stage.{u} := lt_wellFounded.fix makeStage

theorem stages_eq (α : Ordinal.{u}) : stages α = makeStage α (fun γ _ => stages γ) :=
  WellFounded.fix_eq lt_wellFounded makeStage α

/-- `x ∈ C(α, β)` の段階 `n` -/
def Cn (α β : Ordinal.{u}) (n : Nat) (x : Ordinal.{u}) : Prop :=
  StageC α (fun γ _ => stages γ) β n x

/-- `x ∈ C(α, β)` -/
def C (α β x : Ordinal.{u}) : Prop := ∃ n, Cn α β n x

/-- `ρ ∈ M^α` -/
def M (α ρ : Ordinal.{u}) : Prop := (stages α).M ρ

/-- `Ξ_m(α)` -/
def Xi (m : Nat) (α : Ordinal.{u}) : Ordinal.{u} := (stages α).Xi m

/-- `Ψ_π(α)` -/
def Psi (π α : Ordinal.{u}) : Ordinal.{u} := (stages α).Psi π

/-- 崩壊先 `π` の底の条件（段によらない形） -/
def Base (π η : Ordinal.{u}) : Prop :=
  (π = Om 0 ∧ 0 < η) ∨ (∃ ζ, succ ζ < Λ ∧ π = Om (succ ζ) ∧ Om ζ < η) ∨
    (∃ m δ, δ ≤ capK m ∧ π = Xi m δ ∧ π < K m ∧ K (m - 1) < η ∧ C δ η δ)

/-- 段 `α` での底の条件（`Ξ_m(δ)` は `δ < α` のときだけ） -/
def BaseA (α π η : Ordinal.{u}) : Prop :=
  (π = Om 0 ∧ 0 < η) ∨ (∃ ζ, succ ζ < Λ ∧ π = Om (succ ζ) ∧ Om ζ < η) ∨
    (∃ m δ, δ < α ∧ δ ≤ capK m ∧ π = Xi m δ ∧ π < K m ∧ K (m - 1) < η ∧ C δ η δ)

/-! ### 定義の展開 -/

theorem stages_C (α β x : Ordinal.{u}) : (stages α).C β x ↔ C α β x := by
  rw [stages_eq α]
  exact Iff.rfl

theorem stages_Xi (m : Nat) (α : Ordinal.{u}) : (stages α).Xi m = Xi m α := rfl

theorem stages_Psi (π α : Ordinal.{u}) : (stages α).Psi π = Psi π α := rfl

theorem M_iff (α ρ : Ordinal.{u}) :
    M α ρ ↔ IsReg ρ ∧ (∀ x, C α ρ x → x < Kabove ρ → x < ρ) ∧ C α ρ α := by
  unfold M
  rw [stages_eq α]
  exact Iff.rfl

theorem Xi_eq (m : Nat) (α : Ordinal.{u}) :
    Xi m α = least (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m) := by
  unfold Xi M
  rw [stages_eq α]
  rfl

theorem baseAt_iff (α π η : Ordinal.{u}) :
    BaseAt α (fun γ _ => stages γ) π η ↔ BaseA α π η := by
  unfold BaseAt BaseA
  apply Iff.intro
  · rintro (h | h | ⟨m, δ, hδ, hc, h1, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, δ, hδ, hc, h1, h2, h3, (stages_C δ η δ).mp h4⟩)
  · rintro (h | h | ⟨m, δ, hδ, hc, h1, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, δ, hδ, hc, h1, h2, h3, (stages_C δ η δ).mpr h4⟩)

theorem Psi_eq (π α : Ordinal.{u}) :
    Psi π α = least (fun η =>
      (BaseA α π η ∧ η < π ∧ ∀ x, C α η x → x < π → x < η) ∨ η = π) := by
  have h : Psi π α = least (fun η =>
      (BaseAt α (fun γ _ => stages γ) π η ∧ η < π ∧ ∀ x, C α η x → x < π → x < η) ∨ η = π) := by
    unfold Psi C Cn
    rw [stages_eq α]
    rfl
  rw [h]
  congr 1
  funext η
  rw [baseAt_iff]

theorem BaseA.base {α π η : Ordinal.{u}} (h : BaseA α π η) : Base π η := by
  rcases h with h | h | ⟨m, δ, _, hc, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, δ, hc, h1, h2, h3, h4⟩)

theorem BaseA.mono_arg {α α' π η : Ordinal.{u}} (hα : α ≤ α') (h : BaseA α π η) :
    BaseA α' π η := by
  rcases h with h | h | ⟨m, δ, hδ, hc, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, δ, lt_of_lt_of_le hδ hα, hc, h1, h2, h3, h4⟩)

/-! ### `C(α, β)` の構成子 -/

theorem Cn_lt (α β : Ordinal.{u}) (n : Nat) {x : Ordinal.{u}} (h : x < β) : Cn α β n x :=
  StageC.lt n x h

theorem Cn_K (α β : Ordinal.{u}) (n m : Nat) : Cn α β n (K m) := StageC.kc n m

theorem Cn_zero (α β : Ordinal.{u}) (n : Nat) : Cn α β n 0 := Cn_K α β n 0

theorem Cn_succ {α β : Ordinal.{u}} {n : Nat} {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β (n + 1) x := by
  have hadd : Cn α β (n + 1) (x + 0) := StageC.add n x 0 h (Cn_zero α β n)
  rw [add_zero] at hadd
  exact hadd

theorem Cn_mono {α β : Ordinal.{u}} {n m : Nat} (hnm : n ≤ m) {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β m x := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Cn_succ ih

theorem C_lt {α β x : Ordinal.{u}} (h : x < β) : C α β x := Exists.intro 0 (Cn_lt α β 0 h)

theorem C_K (α β : Ordinal.{u}) (m : Nat) : C α β (K m) := Exists.intro 0 (Cn_K α β 0 m)

theorem C_zero (α β : Ordinal.{u}) : C α β 0 := C_K α β 0

theorem C_add {α β x y : Ordinal.{u}} (hx : C α β x) (hy : C α β y) : C α β (x + y) := by
  cases hx with
  | intro n hn =>
    cases hy with
    | intro m hm =>
      exact Exists.intro (max n m + 1) (StageC.add (max n m) x y
        (Cn_mono (Nat.le_max_left n m) hn) (Cn_mono (Nat.le_max_right n m) hm))

theorem C_Om {α β x : Ordinal.{u}} (hΛ : x < Λ) (hx : C α β x) : C α β (Om x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.om n x hΛ hn)

theorem C_Om_zero (α β : Ordinal.{u}) : C α β (Om 0) := C_Om Λ_pos (C_zero α β)

theorem C_Xi {α β x : Ordinal.{u}} (m : Nat) (hα : x < α) (hcap : x ≤ capK m) (hx : C α β x) :
    C α β (Xi m x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.xi n m x hα hcap hn)

theorem C_Psi {α β π δ : Ordinal.{u}} (hα : δ < α) (hπ : IsReg π) (hlt : Psi π δ < π)
    (hnorm : C δ (Psi π δ) δ) (hπC : C α β π) (hδ : C α β δ) : C α β (Psi π δ) := by
  cases hπC with
  | intro m hm =>
    cases hδ with
    | intro k hk =>
      exact Exists.intro (max m k + 1) (StageC.psi (max m k) π δ hα hπ hlt
        ((stages_C δ _ δ).mpr hnorm) (Cn_mono (Nat.le_max_left m k) hm)
        (Cn_mono (Nat.le_max_right m k) hk))

/-! ### 単調性と連続性 -/

theorem Cn_mono_arg {α α' β : Ordinal.{u}} (hα : α ≤ α') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α' β n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ hγ
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hxα hcap _ ih => exact StageC.xi n m x (lt_of_lt_of_le hxα hα) hcap ih
  | psi n π δ hδα hπ hlt hnorm _ _ ihπ ihδ =>
    exact StageC.psi n π δ (lt_of_lt_of_le hδα hα) hπ hlt hnorm ihπ ihδ

theorem C_mono_arg {α α' β x : Ordinal.{u}} (hα : α ≤ α') (h : C α β x) : C α' β x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_arg hα hn)

theorem Cn_mono_base {α β β' : Ordinal.{u}} (hβ : β ≤ β') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α β' n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ (lt_of_lt_of_le hγ hβ)
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hxα hcap _ ih => exact StageC.xi n m x hxα hcap ih
  | psi n π δ hδα hπ hlt hnorm _ _ ihπ ihδ => exact StageC.psi n π δ hδα hπ hlt hnorm ihπ ihδ

theorem C_mono_base {α β β' x : Ordinal.{u}} (hβ : β ≤ β') (h : C α β x) : C α β' x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_base hβ hn)

theorem C_mono {α α' β β' x : Ordinal.{u}} (hα : α ≤ α') (hβ : β ≤ β') (h : C α β x) :
    C α' β' x := C_mono_arg hα (C_mono_base hβ h)

theorem Cn_limit {α β : Ordinal.{u}} (hβ : IsLimit β) {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : ∃ η, η < β ∧ Cn α η n x := by
  unfold Cn at h
  induction h with
  | lt n γ hγ =>
    exact Exists.intro (succ γ) (And.intro (hβ.succ_lt hγ) (StageC.lt n γ (lt_succ_self γ)))
  | kc n m => exact Exists.intro 0 (And.intro hβ.1 (StageC.kc n m))
  | add n x y _ _ ihx ihy =>
    cases ihx with
    | intro η₁ h₁ =>
      cases ihy with
      | intro η₂ h₂ =>
        exact Exists.intro (omax η₁ η₂) (And.intro (omax_lt h₁.1 h₂.1)
          (StageC.add n x y (Cn_mono_base (le_omax_left η₁ η₂) h₁.2)
            (Cn_mono_base (le_omax_right η₁ η₂) h₂.2)))
  | om n x hΛ _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.om n x hΛ h.2))
  | xi n m x hxα hcap _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.xi n m x hxα hcap h.2))
  | psi n π δ hδα hπ hlt hnorm _ _ ihπ ihδ =>
    cases ihπ with
    | intro η₁ h₁ =>
      cases ihδ with
      | intro η₂ h₂ =>
        exact Exists.intro (omax η₁ η₂) (And.intro (omax_lt h₁.1 h₂.1)
          (StageC.psi n π δ hδα hπ hlt hnorm (Cn_mono_base (le_omax_left η₁ η₂) h₁.2)
            (Cn_mono_base (le_omax_right η₁ η₂) h₂.2)))

theorem C_limit {α β x : Ordinal.{u}} (hβ : IsLimit β) (h : C α β x) : ∃ η, η < β ∧ C α η x := by
  cases h with
  | intro n hn =>
    cases Cn_limit hβ hn with
    | intro η hη => exact Exists.intro η (And.intro hη.1 (Exists.intro n hη.2))

/-! ### `Ψ` と `Ξ` の基本的な性質 -/

theorem Psi_le (π α : Ordinal.{u}) : Psi π α ≤ π := by
  rw [Psi_eq]
  exact least_le _ (Or.inr rfl)

/-- `Ψ_π(α) < π` なら底の条件と `C(α, Ψ_π(α)) ∩ π ⊆ Ψ_π(α)` -/
theorem Psi_spec {π α : Ordinal.{u}} (h : Psi π α < π) :
    BaseA α π (Psi π α) ∧ ∀ x, C α (Psi π α) x → x < π → x < Psi π α := by
  have hs := (least_spec (fun η =>
      (BaseA α π η ∧ η < π ∧ ∀ x, C α η x → x < π → x < η) ∨ η = π)
      (Exists.intro π (Or.inr rfl))).1
  rw [← Psi_eq] at hs
  cases hs with
  | inl hs => exact And.intro hs.1 hs.2.2
  | inr he => exact absurd he (ne_of_lt h)

/-- `Ψ_π(α)` は条件を満たす `η < π` 以下 -/
theorem Psi_le_of {π α η : Ordinal.{u}} (hB : BaseA α π η) (hη : η < π)
    (hC : ∀ x, C α η x → x < π → x < η) : Psi π α ≤ η := by
  rw [Psi_eq]
  exact least_le _ (Or.inl ⟨hB, hη, hC⟩)

theorem Psi_eq_of_not_lt {π β : Ordinal.{u}} (h : ¬ Psi π β < π) : Psi π β = π :=
  le_antisymm (Psi_le π β) (le_of_not_lt h)

theorem Xi_le (m : Nat) (α : Ordinal.{u}) : Xi m α ≤ K m := by
  rw [Xi_eq]
  exact least_le _ (Or.inr rfl)

/-- `Ξ_m(α) < K_m` なら `Ξ_m(α) ∈ M^α` で `K_{m-1} < Ξ_m(α)` -/
theorem Xi_spec {m : Nat} {α : Ordinal.{u}} (h : Xi m α < K m) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α := by
  have hs := (least_spec (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    (Exists.intro (K m) (Or.inr rfl))).1
  rw [← Xi_eq] at hs
  cases hs with
  | inl hs => exact And.intro hs.1 hs.2.1
  | inr he => exact absurd he (ne_of_lt h)

/-- `Ξ_m(α)` は条件を満たす `π` 以下 -/
theorem Xi_le_of {m : Nat} {α π : Ordinal.{u}} (hM : M α π) (h1 : K (m - 1) < π) (h2 : π < K m) :
    Xi m α ≤ π := by
  rw [Xi_eq]
  exact least_le _ (Or.inl ⟨hM, h1, h2⟩)

theorem Xi_eq_K_of_not_lt {m : Nat} {x : Ordinal.{u}} (h : ¬ Xi m x < K m) : Xi m x = K m :=
  le_antisymm (Xi_le m x) (le_of_not_lt h)

end

end OCF.Mahlo
