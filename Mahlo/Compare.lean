import Mahlo.Basic

/-! 崩壊関数の値どうしの比較。

* `Xi_lt_Xi_iff`（Rathjen Lemma 4.14）：同じ階の `Ξ` どうしの比較。
* `RegTarget`：崩壊先になる正則基数（`Ω_0`、`Ω_{ζ+1}`、`Ξ_m(δ) < K_m`）。
* `sep`（分離補題、1990 年論文の 5.6 にあたる）：`κ < π` が崩壊先で `Ψ_π(β) < π` なら、
  `Ψ_π(β) ≤ κ` のとき `Ψ_π(β)` は `κ` の底の条件を満たさない。
* `Psi_lt_target_iff`・`Psi_lt_Psi_iff_lt`・`Psi_lt_Psi_same`・`Psi_inj`：`Ψ` の比較と単射性。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen

noncomputable section

variable [Setting.{u}]

/-! ### Lemma 4.14 -/

/-- Lemma 4.14：`Ξ_m(α) < Ξ_m(β)` ⟺ `α < β ∧ α ∈ C(β, Ξ_m(β))` または `β < α ∧ β ∉ C(α, Ξ_m(α))` -/
theorem Xi_lt_Xi_iff {m : Nat} {α β : Ordinal.{u}} (hα : XiGood m α) (hβ : XiGood m β)
    (hcα : α ≤ capK m) (hcβ : β ≤ capK m) :
    Xi m α < Xi m β ↔ (α < β ∧ C β (Xi m β) α) ∨ (β < α ∧ ¬ C α (Xi m α) β) := by
  apply Iff.intro
  · intro hlt
    cases lt_total α β with
    | inl hαβ =>
      exact Or.inl (And.intro hαβ (C_mono_base (Or.inl hlt) (C_mono_arg (Or.inl hαβ) hα.self)))
    | inr h =>
      cases h with
      | inl e => rw [e] at hlt; exact absurd hlt (lt_irrefl _)
      | inr hβα =>
        refine Or.inr (And.intro hβα ?_)
        intro hC
        have hXi : Xi m β < Xi m α := hα.closed _ (C_Xi m hβα hcβ hC) hβ.lt
        exact lt_asymm hlt hXi
  · intro h
    cases h with
    | inl h => exact hβ.closed _ (C_Xi m h.1 hcα h.2) hα.lt
    | inr h =>
      apply lt_of_not_le
      intro hle
      exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base hle hβ.self))

/-- `Ξ_m` は単射 -/
theorem Xi_inj {m : Nat} {α β : Ordinal.{u}} (hα : XiGood m α) (hβ : XiGood m β)
    (hcα : α ≤ capK m) (hcβ : β ≤ capK m) (e : Xi m α = Xi m β) : α = β := by
  cases lt_total α β with
  | inl hαβ =>
    have hC : C β (Xi m β) α := by rw [← e]; exact C_mono_arg (Or.inl hαβ) hα.self
    have hlt := hβ.closed _ (C_Xi m hαβ hcα hC) hα.lt
    rw [e] at hlt
    exact absurd hlt (lt_irrefl _)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr hβα =>
      have hC : C α (Xi m α) β := by rw [e]; exact C_mono_arg (Or.inl hβα) hβ.self
      have hlt := hα.closed _ (C_Xi m hβα hcβ hC) hβ.lt
      rw [e] at hlt
      exact absurd hlt (lt_irrefl _)

/-- 階と引数の両方について単射 -/
theorem Xi_inj' {m m' : Nat} {x x' : Ordinal.{u}} (hX : Xi m x < K m) (hX' : Xi m' x' < K m')
    (hc : x ≤ capK m) (hc' : x' ≤ capK m')
    (e : Xi m x = Xi m' x') : m = m' ∧ x = x' := by
  have g := xiGood_of_lt hX
  have g' := xiGood_of_lt hX'
  have hm : m = m' := by
    have h1 := g.gt
    have h1' := g'.gt
    rw [e] at h1 hX
    have a := K_lt_iff.mp (lt_trans _ _ _ h1 hX')
    have b := K_lt_iff.mp (lt_trans _ _ _ h1' hX)
    omega
  subst hm
  exact And.intro rfl (Xi_inj g g' hc hc' e)

/-! ### 崩壊先 -/

/-- 崩壊先になる正則基数 -/
def RegTarget (κ : Ordinal.{u}) : Prop :=
  κ = Om 0 ∨ (∃ ζ, succ ζ < Λ ∧ κ = Om (succ ζ)) ∨ (∃ m δ, δ ≤ capK m ∧ κ = Xi m δ ∧ Xi m δ < K m)


theorem RegTarget.isReg {κ : Ordinal.{u}} (h : RegTarget κ) : IsReg κ := by
  rcases h with h | ⟨ζ, hζ, h⟩ | ⟨m, δ, _, h, hX⟩
  · rw [h]; exact isReg_Om_zero
  · rw [h]; exact isReg_Om_succ hζ
  · rw [h]; exact (xiGood_of_lt hX).reg

theorem Xi_ne_Om_zero {m : Nat} {δ : Ordinal.{u}} (hX : Xi m δ < K m) : Xi m δ ≠ Om 0 := by
  intro e
  have hf := (xiGood_of_lt hX).fixed
  rw [e] at hf
  have h := Om_inj (Om_lt_Λ Λ_pos) Λ_pos hf
  exact absurd h (ne_of_gt (Om_pos Λ_pos))

theorem Xi_ne_Om_succ {m : Nat} {δ ζ : Ordinal.{u}} (hX : Xi m δ < K m) (hζ : succ ζ < Λ) :
    Xi m δ ≠ Om (succ ζ) := by
  intro e
  have g := xiGood_of_lt hX
  have hf := g.fixed
  rw [e] at hf
  have h := Om_inj (Om_lt_Λ hζ) hζ hf
  have hl := g.isLimit
  rw [e, h] at hl
  exact hl.ne_succ ζ rfl

theorem Om_zero_ne_Om_succ {ζ : Ordinal.{u}} (hζ : succ ζ < Λ) : Om 0 ≠ Om (succ ζ) := by
  intro e
  exact absurd (Om_inj Λ_pos hζ e) (succ_ne_zero ζ).symm

/-- 崩壊先 `κ` は自分自身で底の条件を満たす -/
theorem RegTarget.base_self {κ : Ordinal.{u}} (h : RegTarget κ) : Base κ κ := by
  rcases h with h | ⟨ζ, hζ, h⟩ | ⟨m, δ, hc, h, hX⟩
  · exact Or.inl ⟨h, by rw [h]; exact Om_pos Λ_pos⟩
  · exact Or.inr (Or.inl ⟨ζ, hζ, h, by rw [h]; exact Om_lt_Om (lt_succ_self ζ) hζ⟩)
  · have g := xiGood_of_lt hX
    exact Or.inr (Or.inr ⟨m, δ, hc, h, by rw [h]; exact hX, by rw [h]; exact g.gt,
      by rw [h]; exact g.self⟩)

/-- 崩壊先 `κ` 以上の `η` は `κ` の底の条件を満たす -/
theorem RegTarget.base_of_le {κ η : Ordinal.{u}} (h : RegTarget κ) (hle : κ ≤ η) : Base κ η :=
  h.base_self.mono_base hle

/-- 底の条件は段 `α` の条件と表示によらず移せる：`BaseA α π η₁` と `Base π η₂` から `BaseA α π η₂` -/
theorem BaseA.transfer {α π η₁ η₂ : Ordinal.{u}} (h₁ : BaseA α π η₁) (h₂ : Base π η₂) :
    BaseA α π η₂ := by
  rcases h₁ with ⟨e₁, _⟩ | ⟨ζ, hζ, e₁, _⟩ | ⟨m, δ, hδ, hc, e₁, hX, _, _⟩
  · rcases h₂ with ⟨_, h⟩ | ⟨ζ', hζ', e₂, _⟩ | ⟨m', δ', _, e₂, hX', _, _⟩
    · exact Or.inl ⟨e₁, h⟩
    · exact absurd (e₁.symm.trans e₂) (Om_zero_ne_Om_succ hζ')
    · have hX'' : Xi m' δ' < K m' := by rw [← e₂]; exact hX'
      exact absurd (e₂.symm.trans e₁) (Xi_ne_Om_zero hX'')
  · rcases h₂ with ⟨e₂, _⟩ | ⟨ζ', hζ', e₂, h⟩ | ⟨m', δ', _, e₂, hX', _, _⟩
    · exact absurd (e₂.symm.trans e₁) (Om_zero_ne_Om_succ hζ)
    · have hz := Om_inj hζ hζ' (e₁.symm.trans e₂)
      have hz' : ζ = ζ' := succ_inj hz
      subst hz'
      exact Or.inr (Or.inl ⟨ζ, hζ, e₁, h⟩)
    · have hX'' : Xi m' δ' < K m' := by rw [← e₂]; exact hX'
      exact absurd (e₂.symm.trans e₁) (Xi_ne_Om_succ hX'' hζ)
  · have hXδ : Xi m δ < K m := by rw [← e₁]; exact hX
    rcases h₂ with ⟨e₂, _⟩ | ⟨ζ', hζ', e₂, _⟩ | ⟨m', δ', hc', e₂, hX', h3, h4⟩
    · exact absurd (e₁.symm.trans e₂) (Xi_ne_Om_zero hXδ)
    · exact absurd (e₁.symm.trans e₂) (Xi_ne_Om_succ hXδ hζ')
    · have hX'' : Xi m' δ' < K m' := by rw [← e₂]; exact hX'
      obtain ⟨rfl, rfl⟩ := Xi_inj' hXδ hX'' hc hc' (e₁.symm.trans e₂)
      exact Or.inr (Or.inr ⟨m, δ, hδ, hc, e₁, hX, h3, h4⟩)

/-- `Ψ_π(α) < π` なら `π` は崩壊先 -/
theorem regTarget_of_Psi_lt {π α : Ordinal.{u}} (h : Psi π α < π) : RegTarget π := by
  rcases (Psi_spec h).1 with ⟨e, _⟩ | ⟨ζ, hζ, e, _⟩ | ⟨m, δ, _, hc, e, hX, _, _⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨ζ, hζ, e⟩)
  · exact Or.inr (Or.inr ⟨m, δ, hc, e, by rw [← e]; exact hX⟩)

/-! ### `Ψ` の値の基本的な性質 -/

/-- `Ψ_π(α) < π` なら `π ∈ C(α, Ψ_π(α))` -/
theorem Psi_C_pi {π α : Ordinal.{u}} (h : Psi π α < π) : C α (Psi π α) π := by
  rcases (Psi_spec h).1 with ⟨e, _⟩ | ⟨ζ, hζ, e, hlt⟩ | ⟨m, δ, hδ, hc, e, _, _, hC⟩
  · exact (congrArg (C α (Psi π α)) e).mpr (C_Om_zero _ _)
  · have hζΛ : ζ < Λ := lt_trans _ _ _ (lt_succ_self ζ) hζ
    have hζC : C α (Psi π α) ζ := C_lt (lt_of_le_of_lt (le_Om hζΛ) hlt)
    have h1 : C α (Psi π α) (succ 0) := C_lt (lt_of_lt_of_le (one_lt_Om hζΛ) (Or.inl hlt))
    have hs : C α (Psi π α) (succ ζ) := by rw [← add_one_eq_succ]; exact C_add hζC h1
    exact (congrArg (C α (Psi π α)) e).mpr (C_Om hζ hs)
  · exact (congrArg (C α (Psi π α)) e).mpr (C_Xi m hδ hc (C_mono_arg (Or.inl hδ) hC))

/-- `Ψ_π(α) < π` なら `Ψ_π(α)` は `π` の底の条件を満たす -/
theorem Psi_base {π α : Ordinal.{u}} (h : Psi π α < π) : Base π (Psi π α) := (Psi_spec h).1.base

/-- `Ψ_π(α) < π` なら `Ω_0 ≤ π` で、`π ≠ Ω_0` なら `Ω_0 < Ψ_π(α)` -/
theorem Om_zero_lt_Psi {π α : Ordinal.{u}} (h : Psi π α < π) (hne : π ≠ Om 0) :
    Om 0 < Psi π α := by
  have hR := (regTarget_of_Psi_lt h).isReg.1
  have hle := Om_zero_le_of_R hR
  have hlt : Om 0 < π := lt_of_le_of_ne hle (fun e => hne e.symm)
  exact (Psi_spec h).2 _ (C_Om_zero _ _) hlt

/-- `π` が `Ω` の不動点で `Ψ_π(α) < π` なら `Ω_Ψ = Ψ` -/
theorem Psi_fixed {π α : Ordinal.{u}} (h : Psi π α < π) (hπ : Om π = π) (hΛ : π < Λ) :
    Om (Psi π α) = Psi π α := by
  have sp := Psi_spec h
  have hne : π ≠ Om 0 := by
    intro e
    rw [e] at hπ
    have := Om_inj (Om_lt_Λ Λ_pos) Λ_pos hπ
    exact absurd this (ne_of_gt (Om_pos Λ_pos))
  have hR := (regTarget_of_Psi_lt h).isReg.1
  have hP := Psi_principal_of_lt hR h
  have h0 := Om_zero_lt_Psi h hne
  have hlim : IsLimit (Psi π α) :=
    hP.isLimit (lt_trans _ _ _ one_lt_Om_zero h0)
  apply Om_fixed_of_closed hlim (lt_trans _ _ _ h hΛ)
  intro w hw
  have hwπ : w < π := lt_trans _ _ _ hw h
  apply sp.2 _ (C_Om (lt_trans _ _ _ hwπ hΛ) (C_lt hw))
  have := Om_lt_Om hwπ hΛ
  rw [hπ] at this
  exact this

/-! ### 分離補題 -/

/-- 分離補題：`κ < π` が崩壊先で `Ψ_π(β) < π` なら、`Ψ_π(β) ≤ κ` のとき `¬ Base κ (Ψ_π(β))` -/
theorem sep {π β κ : Ordinal.{u}} (hψ : Psi π β < π) (hκπ : κ < π) (hle : Psi π β ≤ κ)
    (hB : Base κ (Psi π β)) : False := by
  have sp := Psi_spec hψ
  have hcl := sp.2
  rcases hB with ⟨e, _⟩ | ⟨ζ, hζ, e, hlt⟩ | ⟨m, γ, hcγ, e, hX, hK, hCγ⟩
  · -- `κ = Ω_0`
    have := hcl _ (C_Om_zero β _) (by rw [← e]; exact hκπ)
    rw [← e] at this
    exact not_lt_of_le hle this
  · -- `κ = Ω_{ζ+1}`
    have hζΛ : ζ < Λ := lt_trans _ _ _ (lt_succ_self ζ) hζ
    have hζC : C β (Psi π β) ζ := C_lt (lt_of_le_of_lt (le_Om hζΛ) hlt)
    have h1 : C β (Psi π β) (succ 0) := C_lt (lt_of_lt_of_le (one_lt_Om hζΛ) (Or.inl hlt))
    have hs : C β (Psi π β) (succ ζ) := by rw [← add_one_eq_succ]; exact C_add hζC h1
    have := hcl _ (C_Om hζ hs) (by rw [← e]; exact hκπ)
    rw [← e] at this
    exact not_lt_of_le hle this
  · -- `κ = Ξ_m(γ)`
    have hXγ : Xi m γ < K m := by rw [← e]; exact hX
    have gκ := xiGood_of_lt hXγ
    rcases sp.1 with ⟨eπ, _⟩ | ⟨ζ', hζ', eπ, hlt'⟩ | ⟨m', δ, hδ, hcδ, eπ, hX', hK', hCδ⟩
    · -- `π = Ω_0`
      rw [eπ] at hκπ
      rw [e] at hκπ
      exact not_lt_of_le (Om_zero_le_of_R gκ.R) hκπ
    · -- `π = Ω_{ζ'+1}`
      rw [e] at hle hκπ
      have hκΛ : Xi m γ < Λ := gκ.reg.2.1
      obtain ⟨y, hy, ey⟩ := Om_surj (subset_closure gκ.R) hκΛ
      rw [eπ, ← ey] at hκπ
      have hy' : y < succ ζ' := (Om_lt_Om_iff hy hζ').mp hκπ
      have hle' : Om y ≤ Om ζ' :=
        Om_le_Om (le_of_lt_succ hy') (lt_trans _ _ _ (lt_succ_self ζ') hζ')
      rw [← ey] at hle
      exact not_lt_of_le (le_trans hle hle') hlt'
    · -- `π = Ξ_{m'}(δ)`、`δ < β`
      have hXδ : Xi m' δ < K m' := by rw [← eπ]; exact hX'
      have gπ := xiGood_of_lt hXδ
      rw [eπ] at hκπ
      rw [e] at hκπ hle
      have hmm : m = m' := by
        have a1 := gκ.gt
        have a2 := gπ.gt
        have a3 := gκ.lt
        have a4 := gπ.lt
        cases Nat.lt_trichotomy m m' with
        | inl hlt =>
          -- `Ψ > K_{m'-1} ≥ K_m > κ`
          have : K m ≤ K (m' - 1) := K_le (by omega)
          exact absurd (lt_of_le_of_lt (le_trans (Or.inl a3) this) hK') (not_lt_of_le hle)
        | inr h =>
          cases h with
          | inl h => exact h
          | inr hgt =>
            have : K m' ≤ K (m - 1) := K_le (by omega)
            exact absurd (lt_trans _ _ _ hκπ (lt_of_lt_of_le a4 (le_trans this (Or.inl a1))))
              (lt_irrefl _)
      subst hmm
      cases lt_or_le γ β with
      | inl hγβ =>
        have hκC : C β (Psi π β) (Xi m γ) := C_Xi m hγβ hcγ (C_mono_arg (Or.inl hγβ) hCγ)
        have := hcl _ hκC (by rw [eπ]; exact hκπ)
        exact not_lt_of_le hle this
      | inr hβγ =>
        have hδγ : δ < γ := lt_of_lt_of_le hδ hβγ
        cases (Xi_lt_Xi_iff gκ gπ hcγ hcδ).mp hκπ with
        | inl h => exact absurd h.1 (lt_asymm hδγ)
        | inr h =>
          apply h.2
          exact C_mono_arg (Or.inl hδγ) (C_mono_base hle hCδ)

/-- `κ < π` が崩壊先、`Ψ_π(β) < π` なら `Ψ_π(β) < κ ⟺ ¬ Base κ (Ψ_π(β))` -/
theorem Psi_lt_target_iff {π β κ : Ordinal.{u}} (hψ : Psi π β < π) (hκ : RegTarget κ)
    (hκπ : κ < π) : Psi π β < κ ↔ ¬ Base κ (Psi π β) := by
  apply Iff.intro
  · intro hlt hB
    exact sep hψ hκπ (Or.inl hlt) hB
  · intro hnB
    apply lt_of_not_le
    intro hle
    exact hnB (hκ.base_of_le hle)

/-- `κ < π` が崩壊先なら `Ψ_π(β) ≠ κ` -/
theorem Psi_ne_target {π β κ : Ordinal.{u}} (hψ : Psi π β < π) (hκ : RegTarget κ)
    (hκπ : κ < π) : Psi π β ≠ κ := by
  intro e
  exact sep hψ hκπ (Or.inr e) (by rw [e]; exact hκ.base_self)

/-- 崩壊先 `κ` は `Ψ` の値でない -/
theorem Psi_ne_regTarget {π β κ : Ordinal.{u}} (hψ : Psi π β < π) (hκ : RegTarget κ) :
    Psi π β ≠ κ := by
  cases lt_or_le κ π with
  | inl h => exact Psi_ne_target hψ hκ h
  | inr h => exact ne_of_lt (lt_of_lt_of_le hψ h)

/-- 異なる崩壊先 `σ < π` への `Ψ` の比較：`Ψ_π(β) < Ψ_σ(γ) ⟺ ¬ Base σ (Ψ_π(β))` -/
theorem Psi_lt_Psi_iff_lt {π σ β γ : Ordinal.{u}} (hψ : Psi π β < π) (hψ' : Psi σ γ < σ)
    (hσπ : σ < π) : Psi π β < Psi σ γ ↔ ¬ Base σ (Psi π β) := by
  have hσ := regTarget_of_Psi_lt hψ'
  have hBσ := Psi_base hψ'
  apply Iff.intro
  · intro hlt hB
    exact sep hψ hσπ (Or.inl (lt_trans _ _ _ hlt hψ')) hB
  · intro hnB
    apply lt_of_not_le
    intro hle
    exact hnB (hBσ.mono_base hle)

/-- `σ < π` なら `Ψ_σ(γ) < Ψ_π(β) ⟺ Base σ (Ψ_π(β))` -/
theorem Psi_lt_Psi_iff_gt {π σ β γ : Ordinal.{u}} (hψ : Psi π β < π) (hψ' : Psi σ γ < σ)
    (hσπ : σ < π) : Psi σ γ < Psi π β ↔ Base σ (Psi π β) := by
  have hne : Psi π β ≠ Psi σ γ := by
    intro e
    have hB := Psi_base hψ'
    rw [← e] at hB
    exact sep hψ hσπ (Or.inl (by rw [e]; exact hψ')) hB
  apply Iff.intro
  · intro hlt
    exact (Psi_base hψ').mono_base (Or.inl hlt)
  · intro hB
    cases lt_total (Psi σ γ) (Psi π β) with
    | inl h => exact h
    | inr h =>
      cases h with
      | inl e => exact absurd e.symm hne
      | inr h => exact absurd hB ((Psi_lt_Psi_iff_lt hψ hψ' hσπ).mp h)

/-- 同じ崩壊先の `Ψ` の単調性（両方とも `< π`） -/
theorem Psi_mono {π β γ : Ordinal.{u}} (hβγ : β ≤ γ) (hψ : Psi π β < π) (hψ' : Psi π γ < π) :
    Psi π β ≤ Psi π γ := by
  have spγ := Psi_spec hψ'
  apply Psi_le_of ((Psi_spec hψ).1.transfer spγ.1.base) hψ'
  intro x hx hxπ
  exact spγ.2 x (C_mono_arg hβγ hx) hxπ

/-- 同じ崩壊先の `Ψ` は正規な引数について狭義単調 -/
theorem Psi_lt_Psi_of_lt {π β γ : Ordinal.{u}} (hβγ : β < γ) (hψ : Psi π β < π)
    (hψ' : Psi π γ < π) (hnorm : C β (Psi π β) β) : Psi π β < Psi π γ := by
  have hle := Psi_mono (Or.inl hβγ) hψ hψ'
  have hπ := (regTarget_of_Psi_lt hψ).isReg
  have hC : C γ (Psi π γ) (Psi π β) :=
    C_Psi hβγ hπ hψ hnorm (Psi_C_pi hψ') (C_mono_arg (Or.inl hβγ) (C_mono_base hle hnorm))
  exact (Psi_spec hψ').2 _ hC hψ

/-- 正規な引数の `Ψ` の比較 -/
theorem Psi_lt_Psi_same {π β γ : Ordinal.{u}} (hψ : Psi π β < π) (hψ' : Psi π γ < π)
    (hnβ : C β (Psi π β) β) (hnγ : C γ (Psi π γ) γ) : Psi π β < Psi π γ ↔ β < γ := by
  apply Iff.intro
  · intro hlt
    cases lt_total β γ with
    | inl h => exact h
    | inr h =>
      cases h with
      | inl e => rw [e] at hlt; exact absurd hlt (lt_irrefl _)
      | inr h => exact absurd (Psi_lt_Psi_of_lt h hψ' hψ hnγ) (lt_asymm hlt)
  · intro h
    exact Psi_lt_Psi_of_lt h hψ hψ' hnβ

/-- `Ψ` の単射性（正規な引数、値 `< π`） -/
theorem Psi_inj {π σ β γ : Ordinal.{u}} (hψ : Psi π β < π) (hψ' : Psi σ γ < σ)
    (hnβ : C β (Psi π β) β) (hnγ : C γ (Psi σ γ) γ) (e : Psi π β = Psi σ γ) :
    π = σ ∧ β = γ := by
  have hπσ : π = σ := by
    cases lt_total π σ with
    | inl h =>
      have := (Psi_lt_Psi_iff_gt hψ' hψ h).mpr (by rw [← e]; exact Psi_base hψ)
      rw [e] at this
      exact absurd this (lt_irrefl _)
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h =>
        have := (Psi_lt_Psi_iff_gt hψ hψ' h).mpr (by rw [e]; exact Psi_base hψ')
        rw [e] at this
        exact absurd this (lt_irrefl _)
  subst hπσ
  refine And.intro rfl ?_
  cases lt_total β γ with
  | inl h =>
    have := Psi_lt_Psi_of_lt h hψ hψ' hnβ
    rw [e] at this
    exact absurd this (lt_irrefl _)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h =>
      have := Psi_lt_Psi_of_lt h hψ' hψ hnγ
      rw [e] at this
      exact absurd this (lt_irrefl _)

/-! ### 崩壊が値をとる条件 -/

theorem Psi_Om_zero_lt (α : Ordinal.{u}) : Psi (Om 0) α < Om 0 :=
  Psi_lt Om_zero_R (Or.inl ⟨rfl, lt_succ_self 0⟩) one_lt_Om_zero

theorem Psi_Om_succ_lt {ζ : Ordinal.{u}} (hζ : succ ζ < Λ) (α : Ordinal.{u}) :
    Psi (Om (succ ζ)) α < Om (succ ζ) := by
  have hζΛ : ζ < Λ := lt_trans _ _ _ (lt_succ_self ζ) hζ
  have hlt : Om ζ < Om (succ ζ) := Om_lt_Om (lt_succ_self ζ) hζ
  have hl := (Om_succ_R hζ).2.1
  exact Psi_lt (Om_succ_R hζ) (Or.inr (Or.inl ⟨ζ, hζ, rfl, lt_succ_self _⟩)) (hl.succ_lt hlt)

/-- `δ < α` で `Ξ_m(δ) < K_m` なら `Ψ_{Ξ_m(δ)}(α) < Ξ_m(δ)` -/
theorem Psi_Xi_lt {m : Nat} {δ α : Ordinal.{u}} (hX : Xi m δ < K m) (hc : δ ≤ capK m)
    (hδα : δ < α) :
    Psi (Xi m δ) α < Xi m δ := by
  have g := xiGood_of_lt hX
  cases C_limit g.isLimit g.self with
  | intro η hη =>
    let η₀ := omax η (succ (K (m - 1)))
    have hη₀ : η₀ < Xi m δ := omax_lt hη.1 (g.isLimit.succ_lt g.gt)
    apply Psi_lt g.R _ hη₀
    refine Or.inr (Or.inr ⟨m, δ, hδα, hc, rfl, hX, ?_, C_mono_base (le_omax_left _ _) hη.2⟩)
    exact lt_of_lt_of_le (lt_succ_self _) (le_omax_right _ _)

/-- `δ ≥ α` なら `Ψ_{Ξ_m(δ)}(α) = Ξ_m(δ)` -/
theorem Psi_Xi_eq_of_le {m : Nat} {δ α : Ordinal.{u}} (hX : Xi m δ < K m) (hc : δ ≤ capK m)
    (hαδ : α ≤ δ) :
    Psi (Xi m δ) α = Xi m δ := by
  apply Psi_eq_of_not_lt
  intro hlt
  rcases (Psi_spec hlt).1 with ⟨e, _⟩ | ⟨ζ, hζ, e, _⟩ | ⟨m', δ', hδ', hc', e, hX', _, _⟩
  · exact Xi_ne_Om_zero hX e
  · exact Xi_ne_Om_succ hX hζ e
  · have h := Xi_inj' hX (by rw [← e]; exact hX') hc hc' e
    obtain ⟨_, rfl⟩ := h
    exact absurd hδ' (not_lt_of_le hαδ)

end

end OCF.Mahlo
