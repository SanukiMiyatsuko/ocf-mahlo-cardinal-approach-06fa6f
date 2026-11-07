import Mahlo.Agree

/-! 設計の議論で求めた性質の、大基数の仮定なしの形と、崩壊関数の意味論が古典論理を要る理由。

* 比較の規則（設計の §4「比較が Base の判定に帰着します」と Lemma 4.14）を、仮定なしの値 `ordVal` について
  示す。崩壊関数の値 `val` について同じ規則を示したのが `Compare.lean`（`Setting` の下）。
* `1 = Ψ_{Ω_0}(0)`：`one` の下の標準形は `0` だけ（`ordVal` で値 `1` の位置）。
* 崩壊関数 `Ψ_π(α) := min{η < π : ⋯}`・`Ξ_n(α) := min(⋯)`・`Ω` の数え上げは順序数の部分集合の最小元で
  定める。順序数の最小元の原理は排中律を導く（`em_of_exists_min`。この定理自身は `Classical.choice` を
  使わない）。Lean で排中律を得る手段は `Classical.choice` だけなので、崩壊関数を値として持つ意味論
  （`Setting.lean` 以降）は `Classical.choice` を避けられない。記法系の側は全て `propext`・`Quot.sound`
  だけで示してある。 -/

namespace OCF.Mahlo

universe u

open MahloOCF

/-! ### 崩壊関数の意味論が古典論理を要る理由 -/

/-- 1 点の整列順序 -/
def unitWellOrder : WellOrder.{u} where
  Carrier := PUnit.{u + 1}
  lt := fun _ _ => False
  irrefl := fun _ h => h
  trans := fun _ _ _ h _ => h
  total := fun a b => Or.inr (Or.inl (by cases a; cases b; rfl))
  wellFounded := ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩

/-- 順序数の最小元の原理は排中律を導く（`Classical.choice` を使わない証明）。
    `Ψ`・`Ξ`・`Ω` を最小元で定める意味論は、この原理（`Rathjen.least_spec`）を使う。 -/
theorem em_of_exists_min
    (H : ∀ P : Ordinal.{u} → Prop, (∃ ξ, P ξ) → ∃ μ, P μ ∧ ∀ ξ, ξ < μ → ¬ P ξ) (p : Prop) :
    p ∨ ¬ p := by
  have hlt : Ordinal.type (unitWellOrder.below PUnit.unit) < Ordinal.type unitWellOrder :=
    WellOrder.below_self unitWellOrder PUnit.unit
  obtain ⟨μ, hμ, hmin⟩ := H
    (fun ξ => (ξ = Ordinal.type (unitWellOrder.below PUnit.unit) ∧ p) ∨
      ξ = Ordinal.type unitWellOrder) ⟨_, Or.inr rfl⟩
  rcases hμ with ⟨-, hp⟩ | rfl
  · exact Or.inl hp
  · exact Or.inr (fun hp => hmin _ hlt (Or.inl ⟨rfl, hp⟩))

/-- 崩壊関数の定義に使う最小元の関数 `least` があれば排中律が成り立つ -/
theorem em_of_least (p : Prop) : p ∨ ¬ p :=
  em_of_exists_min.{0} (fun P h => ⟨Rathjen.least P, (Rathjen.least_spec P h).1,
    (Rathjen.least_spec P h).2⟩) p

/-! ### 比較の規則（仮定なし） -/

theorem nfLt_iff {a b : NF} : NFLt a b ↔ Lt a.1 b.1 := by
  unfold NFLt MahloOCF.lt Lt
  simp only [beq_iff_eq]

theorem ordVal_lt_iff_Lt (a b : NF) : ordVal a < ordVal b ↔ Lt a.1 b.1 :=
  (ordVal_lt_iff a b).trans nfLt_iff

/-- 同じ崩壊先の `Ψ` は引数で比べる：`Ψ_π(a) < Ψ_π(b) ⟺ a < b` -/
theorem ordVal_psi_same {π : Tm} (a b : NF) (ha : isNF (.Psi π a.1) = true)
    (hb : isNF (.Psi π b.1) = true) :
    ordVal ⟨.Psi π a.1, ha⟩ < ordVal ⟨.Psi π b.1, hb⟩ ↔ ordVal a < ordVal b := by
  rw [ordVal_lt_iff_Lt, ordVal_lt_iff_Lt]
  exact lt_psi_psi_same

/-- 同じ階の `Ξ` どうしの比較（Lemma 4.14）：`Ξ_n(a) < Ξ_n(b) ⟺ (a < b ∧ a ∈ C(b, Ξ_n(b))) ∨
    (b < a ∧ b ∉ C(a, Ξ_n(a)))` -/
theorem ordVal_xi_xi {n : Nat} (a b : NF) (hne : a ≠ b) (ha : isNF (.Xi n a.1) = true)
    (hb : isNF (.Xi n b.1) = true) :
    ordVal ⟨.Xi n a.1, ha⟩ < ordVal ⟨.Xi n b.1, hb⟩ ↔
      (ordVal a < ordVal b ∧ inC a.1 b.1 (.Xi n b.1) = true) ∨
        (ordVal b < ordVal a ∧ inC b.1 a.1 (.Xi n a.1) = false) := by
  rw [ordVal_lt_iff_Lt, ordVal_lt_iff_Lt, ordVal_lt_iff_Lt]
  exact lt_xi_xi0 (fun e => hne (Subtype.ext e))

/-- 崩壊先 `σ < π`（同じ階）：`Ψ_π(a) < Ψ_σ(b) ⟺ ¬ Base_σ(Ψ_π(a))` -/
theorem ordVal_psi_psi_of_target_lt {π σ a b : Tm} (hl : lev π = lev σ)
    (ha : isNF (.Psi π a) = true) (hb : isNF (.Psi σ b) = true)
    (hσπ : ordVal ⟨σ, (WNF.psi hb).piF⟩ < ordVal ⟨π, (WNF.psi ha).piF⟩) :
    ordVal ⟨.Psi π a, ha⟩ < ordVal ⟨.Psi σ b, hb⟩ ↔ baseOf σ (.Psi π a) = false := by
  rw [ordVal_lt_iff_Lt] at hσπ
  have h' : Lt σ π := hσπ
  rw [ordVal_lt_iff_Lt]
  exact lt_psi_psi_gtT hl (fun e => by subst e; exact Lt.irrefl _ h') h'

/-- 崩壊先 `π < σ`（同じ階）：`Ψ_π(a) < Ψ_σ(b) ⟺ Base_π(Ψ_σ(b))` -/
theorem ordVal_psi_psi_of_lt_target {π σ a b : Tm} (hl : lev π = lev σ)
    (ha : isNF (.Psi π a) = true) (hb : isNF (.Psi σ b) = true)
    (hπσ : ordVal ⟨π, (WNF.psi ha).piF⟩ < ordVal ⟨σ, (WNF.psi hb).piF⟩) :
    ordVal ⟨.Psi π a, ha⟩ < ordVal ⟨.Psi σ b, hb⟩ ↔ baseOf π (.Psi σ b) = true := by
  rw [ordVal_lt_iff_Lt] at hπσ
  have h' : Lt π σ := hπσ
  rw [ordVal_lt_iff_Lt]
  exact lt_psi_psi_ltT hl (fun e => by subst e; exact Lt.irrefl _ h')
    (Lt.asymmY (WNF.psi ha).piF (WNF.psi hb).piF h')

/-- 正則な `κ = Ξ_n(c) < π`（同じ階）：`Ψ_π(a) < κ ⟺ ¬ Base_κ(Ψ_π(a))` -/
theorem ordVal_psi_xi_of_lt_target {π a c : Tm} {n : Nat} (hl : lev π = n)
    (ha : isNF (.Psi π a) = true) (hc : isNF (.Xi n c) = true)
    (hκπ : ordVal ⟨.Xi n c, hc⟩ < ordVal ⟨π, (WNF.psi ha).piF⟩) :
    ordVal ⟨.Psi π a, ha⟩ < ordVal ⟨.Xi n c, hc⟩ ↔ baseOf (.Xi n c) (.Psi π a) = false := by
  rw [ordVal_lt_iff_Lt] at hκπ
  rw [ordVal_lt_iff_Lt, lt_psi_xiY hl]
  have hgt : cmp π (.Xi n c) = .gt := by
    have e := swapY hc (WNF.psi ha).piF
    unfold Lt at hκπ
    rw [hκπ] at e
    exact e
  rw [hgt]
  simp

/-- `1 = Ψ_{Ω_0}(0)`：`1` の下の標準形は `0` だけ -/
theorem ordVal_lt_one (x : NF) : ordVal x < ordVal ⟨one, WNF.one⟩ ↔ x.1 = .zero := by
  rw [ordVal_lt_iff_Lt]
  constructor
  · intro h
    match decEq x.1 .zero with
    | isTrue h0 => exact h0
    | isFalse h0 =>
      rcases one_leY x.2 h0 with e | h'
      · rw [← e] at h
        exact absurd h (Lt.irrefl _)
      · exact absurd h' (Lt.asymmY x.2 WNF.one h)
  · intro e
    show Lt x.1 one
    rw [e]
    rcases triY WNF.zero WNF.one with h | h | h
    · exact h
    · cases h
    · exact absurd h (MahloOCF.not_lt_zero one)

/-- 到達不能基数 `π = Ξ_n(d)` への崩壊では `Ψ_π(b)·(k+1)` は `Ψ_π(c)`（`b < c`）の基本列にならない：
    その全てより大きく `Ψ_π(c)` より小さい標準形 `Ω_{Ψ_π(b)+1}` がある（設計の「到達不能基数への Ψ は
    Ω の入れ子で、·ω にはできない」） -/
theorem psi_xi_fs_not_cofinal {n : Nat} {d b c : Tm} (hb : isNF (.Psi (.Xi n d) b) = true)
    (hc : isNF (.Psi (.Xi n d) c) = true) (hbc : MahloOCF.lt b c = true) :
    ∃ x : NF, MahloOCF.lt x.1 (.Psi (.Xi n d) c) = true ∧
      ∀ k, MahloOCF.lt (fsTerm (.Xi n d) b k) x.1 = true := by
  have toLt : ∀ {a b : Tm}, MahloOCF.lt a b = true ↔ Lt a b := by
    intro a b
    unfold MahloOCF.lt Lt
    simp only [beq_iff_eq]
  obtain ⟨h1, h2, h3⟩ := psi_xi_gapY hb hc (toLt.mp hbc)
  exact ⟨⟨_, h1⟩, toLt.mpr h3, fun k => toLt.mpr (h2 k)⟩

/-! ### 有効性の制限と Rathjen 型の条件（設計 §5 の 1 つ目）

設計では「`Ξ_n(δ)` への崩壊は引数が `δ` より大きいときしか効かないが、Compact（Rathjen 型）の条件
`π ∈ C(α,ρ)` も同じ制限を課すので失うものはない」とした。その根拠を示す：`ρ < π = Ξ_k(γ)` のとき
`π ∈ C(α,ρ) ⟺ γ < α ∧ γ ∈ C(α,ρ)`。特に `α ≤ γ` なら Rathjen 型の条件を満たす `ρ < π` はなく、Rathjen 型の
`Ψ_π(α)` も値を持たない（この体系の `Psi_Xi_eq_of_le` と同じ）。 -/

section Effective

open Ordinal Rathjen

variable [Setting.{u}]

theorem mem_C_Xi_aux {α ρ γ : Ordinal.{u}} {k : Nat} (hX : Xi k γ < K k) (hc : γ ≤ capK k)
    (hρ : ρ < Xi k γ) : ∀ n x, Cn α ρ n x → x = Xi k γ → γ < α ∧ C α ρ γ := by
  have g := xiGood_of_lt hX
  have hp : IsPrincipal (Xi k γ) := (Xi_principal_or_zero k γ).resolve_left (fun h0 => by
    have := g.gt
    rw [h0] at this
    exact Ordinal.not_lt_zero _ this)
  have hΛ : Xi k γ < Λ := Ordinal.lt_trans _ _ _ hX (K_lt_Λ k)
  have small : ∀ x, x < ρ → x = Xi k γ → False := fun x h e => by
    rw [e] at h
    exact Ordinal.lt_irrefl _ (Ordinal.lt_trans _ _ _ h hρ)
  intro n
  induction n with
  | zero =>
    intro x hx e
    rcases Cn_zero_cases hx with h | ⟨m, rfl⟩
    · exact (small x h e).elim
    · exact absurd e.symm (Xi_ne_K hX)
  | succ n ih =>
    intro x hx e
    unfold Cn at hx
    cases hx with
    | lt _ _ h => exact (small x h e).elim
    | kc _ m => exact absurd e.symm (Xi_ne_K hX)
    | add _ y z hy hz =>
      cases lt_or_le y (Xi k γ) with
      | inl hy' =>
        cases lt_or_le z (Xi k γ) with
        | inl hz' =>
          have := hp.2 y z hy' hz'
          rw [e] at this
          exact (Ordinal.lt_irrefl _ this).elim
        | inr hz' =>
          have hzle : z ≤ Xi k γ := by rw [← e]; exact right_le_add y z
          exact ih z hz (le_antisymm hzle hz')
      | inr hy' =>
        have hyle : y ≤ Xi k γ := by rw [← e]; exact le_add y z
        exact ih y hy (le_antisymm hyle hy')
    | om _ y hyΛ hy =>
      exact ih y hy (Om_inj hyΛ hΛ (e.trans g.fixed.symm))
    | xi _ m y hα hcap hy =>
      have e' : Xi m y = Xi k γ := e
      have hXm : Xi m y < K m := by
        cases Xi_le m y with
        | inl h => exact h
        | inr h => exact absurd (e'.symm.trans h) (Xi_ne_K hX)
      obtain ⟨rfl, rfl⟩ := Xi_inj' hXm hX hcap hc e'
      exact ⟨hα, ⟨n, hy⟩⟩
    | psi _ π δ hα hπ hlt hnorm hπC hδ =>
      have hlt' : Psi π δ < π := hlt
      exact absurd e (Psi_ne_regTarget hlt' (Or.inr (Or.inr ⟨k, γ, hc, rfl, hX⟩)))

/-- Rathjen 型の条件 `π ∈ C(α, ρ)`（`π = Ξ_k(γ)`、`ρ < π`）は、この体系の有効性 `γ < α`（と `γ ∈ C(α,ρ)`）と
    同値 -/
theorem Xi_mem_C_iff {α ρ γ : Ordinal.{u}} {k : Nat} (hX : Xi k γ < K k) (hc : γ ≤ capK k)
    (hρ : ρ < Xi k γ) : C α ρ (Xi k γ) ↔ γ < α ∧ C α ρ γ :=
  ⟨fun ⟨n, h⟩ => mem_C_Xi_aux hX hc hρ n _ h rfl, fun ⟨h1, h2⟩ => C_Xi k h1 hc h2⟩

/-- `α ≤ γ` なら Rathjen 型の条件 `Ξ_k(γ) ∈ C(α, ρ)` を満たす `ρ < Ξ_k(γ)` はない（Rathjen 型の
    `Ψ_{Ξ_k(γ)}(α)` も値を持たない） -/
theorem rathjen_no_candidate {α γ : Ordinal.{u}} {k : Nat} (hX : Xi k γ < K k) (hc : γ ≤ capK k)
    (hαγ : α ≤ γ) (ρ : Ordinal.{u}) (hρ : ρ < Xi k γ) : ¬ C α ρ (Xi k γ) := fun h =>
  Ordinal.lt_irrefl _ (lt_of_lt_of_le ((Xi_mem_C_iff hX hc hρ).mp h).1 hαγ)

/-- この体系の `Ψ_π(α)` は Rathjen 型の条件 `π ∈ C(α, Ψ_π(α))` を満たす -/
theorem Psi_rathjen_condition {π α : Ordinal.{u}} (h : Psi π α < π) : C α (Psi π α) π :=
  Psi_C_pi h

end Effective

/-- `0` は最小 -/
theorem not_ordVal_lt_zero (x : NF) : ¬ ordVal x < ordVal ⟨.zero, WNF.zero⟩ := by
  rw [ordVal_lt_iff_Lt]
  exact MahloOCF.not_lt_zero x.1

end OCF.Mahlo

/-- info: 'OCF.Mahlo.em_of_exists_min' depends on axioms: [propext] -/
#guard_msgs in #print axioms OCF.Mahlo.em_of_exists_min

/-- info: 'OCF.Mahlo.ordVal_psi_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_psi_same

/-- info: 'OCF.Mahlo.ordVal_xi_xi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_xi_xi

/-- info: 'OCF.Mahlo.ordVal_psi_psi_of_target_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_psi_psi_of_target_lt

/-- info: 'OCF.Mahlo.ordVal_psi_psi_of_lt_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_psi_psi_of_lt_target

/-- info: 'OCF.Mahlo.ordVal_psi_xi_of_lt_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_psi_xi_of_lt_target

/-- info: 'OCF.Mahlo.ordVal_lt_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_lt_one

/-- info: 'OCF.Mahlo.psi_xi_fs_not_cofinal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.psi_xi_fs_not_cofinal

/-- info: 'OCF.Mahlo.not_ordVal_lt_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.not_ordVal_lt_zero
