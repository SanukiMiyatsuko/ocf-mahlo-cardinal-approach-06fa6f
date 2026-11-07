import Mahlo.Setting

/-! `C(α, β)` の大きさ、閉非有界集合、`Ξ`・`Ψ` が値をとること。

* `C_small`・`C_bounded`：`π` が非可算正則で `β < π` なら `|C(α, β)| < π`。
* `club_closedC`：`C(α, ρ) ∩ π ⊆ ρ` となる `ρ` は `π` で閉非有界。
* `Xi_lt`：`α ∈ C(α, K_m)` なら `Ξ_m(α) < K_m`（`K_m` が弱 Mahlo であることを使う）。
* `Psi_lt`：底の条件を満たす `η₀ < π` があれば `Ψ_π(α) < π`。
* `Psi_Om_zero_zero`：`Ψ_{Ω_0}(0) = 1`。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen

noncomputable section

variable [Setting.{u}]

/-! ### `|C(α, β)| < π` -/

theorem Cn_zero_cases {α β x : Ordinal.{u}} (h : Cn α β 0 x) : x < β ∨ ∃ m, x = K m := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl h
  | kc _ m => exact Or.inr (Exists.intro m rfl)

theorem Cn_succ_cases {α β x : Ordinal.{u}} {n : Nat} (h : Cn α β (n + 1) x) :
    Cn α β n x ∨ (∃ y z, Cn α β n y ∧ Cn α β n z ∧ x = y + z) ∨
      (∃ y, Cn α β n y ∧ x = Om y) ∨
      (∃ y m, Cn α β n y ∧ x = Xi m y) ∨
      (∃ π δ, Cn α β n π ∧ Cn α β n δ ∧ x = Psi π δ) := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl (StageC.lt n x h)
  | kc _ m => exact Or.inl (StageC.kc n m)
  | add _ y z hy hz => exact Or.inr (Or.inl ⟨y, z, hy, hz, rfl⟩)
  | om _ y _ hy => exact Or.inr (Or.inr (Or.inl ⟨y, hy, rfl⟩))
  | xi _ m y _ _ hy => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, m, hy, rfl⟩)))
  | psi _ π δ _ _ _ _ hπ hδ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨π, δ, hπ, hδ, rfl⟩)))

theorem small_K {κ : Ordinal.{u}} (hω : omega < κ) : Small κ (fun x => ∃ m, x = K m) := by
  apply ((small_natOrd hω).image (fun y => K (natOf y))).mono
  intro x hx
  cases hx with
  | intro m hm =>
    refine Exists.intro (ordNat m) (And.intro (Exists.intro m rfl) ?_)
    rw [natOf_ordNat]
    exact hm

theorem Cn_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∀ n, Small π (Cn α β n) := by
  have hreg := hπ.2
  have hω := hπ.1
  intro n
  induction n with
  | zero =>
    apply (Small.union hreg (small_lt hβ) (small_K hω)).mono
    intro x hx
    exact Cn_zero_cases hx
  | succ n ih =>
    have hadd := Small.image2 hreg ih ih (fun y z => y + z)
    have hom := Small.image ih Om
    have hxi := Small.image2 hreg ih (small_natOrd hω) (fun y m => Xi (natOf m) y)
    have hpsi := Small.image2 hreg ih ih (fun p d => Psi p d)
    apply (Small.union hreg ih (Small.union hreg hadd (Small.union hreg hom
      (Small.union hreg hxi hpsi)))).mono
    intro x hx
    rcases Cn_succ_cases hx with h | h | ⟨y, hy, e⟩ | ⟨y, m, hy, e⟩ | ⟨p, d, hp, hd, e⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, e⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨y, ordNat m, hy, Exists.intro m rfl, ?_⟩)))
      rw [natOf_ordNat]
      exact e
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, d, hp, hd, e⟩)))

/-- `|C(α, β)| < π` -/
theorem C_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    Small π (C α β) := by
  apply (Small.iUnion hπ.2 (small_natOrd hπ.1) (A := fun i x => Cn α β (natOf i) x)
    (fun i _ => Cn_small hπ hβ α (natOf i))).mono
  intro x hx
  cases hx with
  | intro n hn =>
    refine Exists.intro (ordNat n) (And.intro (Exists.intro n rfl) ?_)
    show Cn α β (natOf (ordNat n)) x
    rw [natOf_ordNat]
    exact hn

/-- `C(α, β) ∩ π` は `π` 未満で抑えられる -/
theorem C_bounded {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∃ γ, γ < π ∧ ∀ x, C α β x → x < π → x < γ := by
  cases Small.bounded hπ.2 ((C_small hπ hβ α).mono (A := fun x => C α β x ∧ x < π)
      (fun _ h => h.1)) (fun _ h => h.2) with
  | intro γ hγ => exact Exists.intro γ (And.intro hγ.1 (fun x hx hxπ => hγ.2 x (And.intro hx hxπ)))

/-- `C(α, ρ) ∩ π ⊆ ρ` となる `ρ`（`μ₀ < ρ < π`）は `π` で閉非有界 -/
theorem club_closedC {π : Ordinal.{u}} (hπ : R π) (α : Ordinal.{u}) {μ₀ : Ordinal.{u}}
    (hμ₀ : μ₀ < π) :
    Club π (fun ρ => μ₀ < ρ ∧ ∀ x, C α ρ x → x < π → x < ρ) := by
  classical
  apply And.intro
  · intro η hη
    let bnd : Ordinal.{u} → Ordinal.{u} := fun δ =>
      if h : δ < π then Classical.choose (C_bounded hπ h α) else 0
    have hbnd : ∀ δ, δ < π → bnd δ < π ∧ ∀ x, C α δ x → x < π → x < bnd δ := by
      intro δ hδ
      have e : bnd δ = Classical.choose (C_bounded hπ hδ α) := dite_eq_left hδ
      rw [e]
      exact Classical.choose_spec (C_bounded hπ hδ α)
    let s : Nat → Ordinal.{u} := fun n =>
      Nat.rec (succ (omax η μ₀)) (fun _ δ => omax (succ δ) (bnd δ)) n
    have hs0 : s 0 = succ (omax η μ₀) := rfl
    have hsS : ∀ n, s (n + 1) = omax (succ (s n)) (bnd (s n)) := fun _ => rfl
    have hsπ : ∀ n, s n < π := by
      intro n
      induction n with
      | zero => rw [hs0]; exact hπ.2.1.succ_lt (omax_lt hη hμ₀)
      | succ n ih =>
        rw [hsS]
        exact omax_lt (hπ.2.1.succ_lt ih) (hbnd _ ih).1
    have hs : ∀ n, s n < s (n + 1) := by
      intro n
      rw [hsS]
      exact lt_of_lt_of_le (lt_succ_self _) (le_omax_left _ _)
    let δs := omegaSup s
    have hδsπ : δs < π := omegaSup_lt hπ hsπ
    have hδslim : IsLimit δs := by
      apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn => exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    have hlt0 : omax η μ₀ < δs := lt_trans _ _ _ (lt_succ_self _) (lt_omegaSup hs 0)
    refine Exists.intro δs (And.intro (And.intro
      (lt_of_le_of_lt (le_omax_right η μ₀) hlt0) ?_)
      (And.intro (lt_of_le_of_lt (le_omax_left η μ₀) hlt0) hδsπ))
    intro x hx hxπ
    cases C_limit hδslim hx with
    | intro ζ hζ =>
      cases (lt_omegaSup_iff ζ).mp hζ.1 with
      | intro n hn =>
        have hxn : x < bnd (s n) := (hbnd _ (hsπ n)).2 x (C_mono_base (Or.inl hn) hζ.2) hxπ
        exact lt_trans _ _ _ hxn (lt_of_le_of_lt (by rw [hsS n]; exact le_omax_right _ _)
          (lt_omegaSup hs (n + 1)))
  · intro l hlπ hlp
    have hl : IsLimit l := by
      apply And.intro hlp.1
      intro β hβ
      cases hlp.2 β hβ with
      | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2
    apply And.intro
    · cases hlp.2 0 hlp.1 with
      | intro γ hγ => exact lt_trans _ _ _ hγ.1.1 hγ.2.2
    · intro x hx hxπ
      cases C_limit hl hx with
      | intro ζ hζ =>
        cases hlp.2 ζ hζ.1 with
        | intro ρ hρ =>
          exact lt_trans _ _ _ (hρ.1.2 x (C_mono_base (Or.inl hρ.2.1) hζ.2) hxπ) hρ.2.2

/-! ### 階と `K(ρ)` -/

theorem exists_level_aux (π : Ordinal.{u}) :
    ∀ N, π < K N → ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (not_lt_zero π)
  | succ N ih =>
    intro h
    cases lt_or_le π (K N) with
    | inl h' => exact ih h'
    | inr h' =>
      refine Exists.intro (N + 1) (And.intro h ?_)
      intro m hm
      exact le_trans (K_le (Nat.le_of_lt_succ hm)) h'

/-- `π < Λ` なら `π < K_n` となる最小の `n` がある -/
theorem exists_level {π : Ordinal.{u}} (hπ : π < Λ) : ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  cases (lt_Λ_iff π).mp hπ with
  | intro N hN => exact exists_level_aux π N hN

/-- `π < Λ` なら `K_{n-1} ≤ π < K_n` となる `n ≥ 1` がある -/
theorem exists_level' {π : Ordinal.{u}} (hπ : π < Λ) : ∃ n, 1 ≤ n ∧ K (n - 1) ≤ π ∧ π < K n := by
  cases exists_level hπ with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn.1 (not_lt_zero π)
    | succ n => exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hn.2 n (Nat.lt_succ_self n), hn.1⟩

theorem Kabove_eq {π : Ordinal.{u}} {n : Nat} (h1 : π < K n) (h2 : ∀ m, m < n → K m ≤ π) :
    Kabove π = K n := by
  have hP : (∃ k, K n = K k) ∧ π < K n := And.intro (Exists.intro n rfl) h1
  apply le_antisymm (least_le _ hP)
  apply le_of_not_lt
  intro hlt
  have hs := (least_spec (fun κ => (∃ k, κ = K k) ∧ π < κ) (Exists.intro _ hP)).1
  cases hs.1 with
  | intro k hk =>
    have hltk : K k < K n := by rw [← hk]; exact hlt
    have hπk : π < K k := by rw [← hk]; exact hs.2
    exact absurd hπk (not_lt_of_le (h2 k (K_lt_iff.mp hltk)))

/-- `K_{n-1} ≤ ρ < K_n` なら `K(ρ) = K_n` -/
theorem Kabove_eq_of_between {ρ : Ordinal.{u}} {n : Nat} (h1 : K (n - 1) ≤ ρ)
    (h2 : ρ < K n) : Kabove ρ = K n := by
  apply Kabove_eq h2
  intro m hm
  exact le_trans (K_le (Nat.le_sub_one_of_lt hm)) h1

/-- `π ∈ Reg` なら `K_{n-1} < π < K_n`（`1 ≤ n`）となる `n` があり、`K(π) = K_n` -/
theorem IsReg.level {π : Ordinal.{u}} (hπ : IsReg π) :
    ∃ n, 1 ≤ n ∧ K (n - 1) < π ∧ π < K n ∧ Kabove π = K n := by
  cases exists_level hπ.2.1 with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn.1 (not_lt_zero π)
    | succ n =>
      have hle : K n ≤ π := hn.2 n (Nat.lt_succ_self n)
      have hlt : K n < π := lt_of_le_of_ne hle (fun e => hπ.2.2 n e.symm)
      exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hlt, hn.1, Kabove_eq hn.1 hn.2⟩

/-! ### 正則な崩壊先 -/

theorem K_ne_Om_zero (n : Nat) : K.{u} n ≠ Om 0 := by
  intro e
  cases n with
  | zero => exact absurd e (ne_of_lt (Om_pos Λ_pos))
  | succ n =>
    have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [← Om_K hn] at e
    have h0 := Om_inj (K_lt_Λ _) Λ_pos e
    exact absurd h0 (ne_of_gt (R_K hn).2.pos)

theorem isReg_Om_zero : IsReg (Om (0 : Ordinal.{u})) :=
  ⟨Om_zero_R, Om_lt_Λ Λ_pos, fun n e => K_ne_Om_zero n e.symm⟩

theorem isReg_Om_succ {ζ : Ordinal.{u}} (hΛ : succ ζ < Λ) : IsReg (Om (succ ζ)) := by
  refine ⟨Om_succ_R hΛ, Om_lt_Λ hΛ, ?_⟩
  intro n e
  cases n with
  | zero => exact absurd e (ne_of_gt (Om_pos hΛ))
  | succ n =>
    have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [← Om_K hn] at e
    have e' := Om_inj hΛ (K_lt_Λ _) e
    exact (R_K hn).2.1.ne_succ ζ e'.symm

/-! ### `Ω` の不動点 -/

/-- `Ω` で閉じた極限 `π < Λ` は `Ω` の不動点 -/
theorem Om_fixed_of_closed {π : Ordinal.{u}} (hl : IsLimit π) (hΛ : π < Λ)
    (h : ∀ w, w < π → Om w < π) : Om π = π := by
  apply le_antisymm _ (le_Om hΛ)
  rw [Om_limit hl hΛ]
  exact (supLt_le_iff π Om π).mpr (fun w hw => Or.inl (h w hw))

/-- `π ∈ M^α` なら `Ω_π = π` -/
theorem M_fixed {α π : Ordinal.{u}} (h : M α π) : Om π = π := by
  have hM := (M_iff α π).mp h
  cases hM.1.level with
  | intro n hn =>
    apply Om_fixed_of_closed hM.1.1.2.1 hM.1.2.1
    intro w hw
    have hwK : w < K n := lt_trans _ _ _ hw hn.2.2.1
    apply hM.2.1 _ (C_Om (lt_trans _ _ _ hwK (K_lt_Λ n)) (C_lt hw))
    rw [hn.2.2.2]
    exact Om_lt_K hn.1 hwK

/-! ### `Ξ_m(α) < K_m`（Mahlo 性） -/

/-- `α ∈ C(α, K_m)` なら `K_{m-1} < Ξ_m(α) < K_m` で `Ξ_m(α) ∈ M^α` -/
theorem Xi_lt {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hC : C α (K m) α) : Xi m α < K m := by
  have hR := R_K hm
  have hlt : K (m - 1) < K m := K_lt (Nat.sub_lt hm Nat.one_pos)
  cases C_limit hR.2.1 hC with
  | intro η₁ h₁ =>
    let μ₀ := omax η₁ (K (m - 1))
    have hμ₀ : μ₀ < K m := omax_lt h₁.1 hlt
    cases (mahlo_K hm).2 _ (club_closedC hR α hμ₀) with
    | intro ρ hρ =>
      have hKρ : K (m - 1) < ρ := lt_of_le_of_lt (le_omax_right _ _) hρ.2.1.1
      have hreg : IsReg ρ := by
        refine ⟨hρ.2.2, lt_trans _ _ _ hρ.1 (K_lt_Λ m), ?_⟩
        intro n e
        rw [e] at hKρ hρ
        have a := K_lt_iff.mp hKρ
        have b := K_lt_iff.mp hρ.1
        omega
      have hKab : Kabove ρ = K m := Kabove_eq_of_between (Or.inl hKρ) hρ.1
      have hM : M α ρ := by
        refine (M_iff α ρ).mpr ⟨hreg, ?_, ?_⟩
        · intro x hx hxK
          rw [hKab] at hxK
          exact hρ.2.1.2 x hx hxK
        · exact C_mono_base (le_trans (le_omax_left _ _) (Or.inl hρ.2.1.1)) h₁.2
      exact lt_of_le_of_lt (Xi_le_of hM hKρ hρ.1) hρ.1

theorem Xi_mem {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hC : C α (K m) α) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α ∧ Xi m α < K m :=
  let h := Xi_spec (Xi_lt hm hC)
  ⟨h.1, h.2, Xi_lt hm hC⟩

/-- `Ξ_m(α) < K_m` なら `1 ≤ m` -/
theorem Xi_level {m : Nat} {x : Ordinal.{u}} (hX : Xi m x < K m) : 1 ≤ m := by
  cases m with
  | zero => exact absurd hX (not_lt_of_le (zero_le _))
  | succ m => exact Nat.succ_le_succ (Nat.zero_le m)

/-- `Ξ_m(α) < K_m` の性質をまとめたもの -/
structure XiGood (m : Nat) (α : Ordinal.{u}) : Prop where
  lt : Xi m α < K m
  gt : K (m - 1) < Xi m α
  reg : IsReg (Xi m α)
  closed : ∀ x, C α (Xi m α) x → x < K m → x < Xi m α
  self : C α (Xi m α) α
  fixed : Om (Xi m α) = Xi m α

theorem xiGood_of_lt {m : Nat} {α : Ordinal.{u}} (h : Xi m α < K m) : XiGood m α := by
  have hs := Xi_spec h
  have hM := (M_iff α _).mp hs.1
  have hKab : Kabove (Xi m α) = K m := Kabove_eq_of_between (Or.inl hs.2) h
  exact {
    lt := h
    gt := hs.2
    reg := hM.1
    closed := fun x hx hxK => hM.2.1 x hx (by rw [hKab]; exact hxK)
    self := hM.2.2
    fixed := M_fixed hs.1 }

theorem XiGood.R {m : Nat} {α : Ordinal.{u}} (h : XiGood m α) : R (Xi m α) := h.reg.1

theorem XiGood.level {m : Nat} {α : Ordinal.{u}} (h : XiGood m α) : 1 ≤ m := Xi_level h.lt

theorem XiGood.isLimit {m : Nat} {α : Ordinal.{u}} (h : XiGood m α) : IsLimit (Xi m α) :=
  h.R.2.1

/-! ### `Ψ_π(α) < π` -/

theorem BaseA.mono_base {α π η η' : Ordinal.{u}} (hη : η ≤ η') (h : BaseA α π η) :
    BaseA α π η' := by
  rcases h with ⟨h1, h2⟩ | ⟨ζ, h1, h2, h3⟩ | ⟨m, δ, hδ, hc, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, lt_of_lt_of_le h2 hη⟩
  · exact Or.inr (Or.inl ⟨ζ, h1, h2, lt_of_lt_of_le h3 hη⟩)
  · exact Or.inr (Or.inr ⟨m, δ, hδ, hc, h1, h2, lt_of_lt_of_le h3 hη, C_mono_base hη h4⟩)

theorem Base.mono_base {π η η' : Ordinal.{u}} (hη : η ≤ η') (h : Base π η) : Base π η' := by
  rcases h with ⟨h1, h2⟩ | ⟨ζ, h1, h2, h3⟩ | ⟨m, δ, hc, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, lt_of_lt_of_le h2 hη⟩
  · exact Or.inr (Or.inl ⟨ζ, h1, h2, lt_of_lt_of_le h3 hη⟩)
  · exact Or.inr (Or.inr ⟨m, δ, hc, h1, h2, lt_of_lt_of_le h3 hη, C_mono_base hη h4⟩)

/-- 底の条件を満たす `η₀ < π` があれば `Ψ_π(α) < π` -/
theorem Psi_lt {π α η₀ : Ordinal.{u}} (hπ : R π) (hB : BaseA α π η₀) (hη₀ : η₀ < π) :
    Psi π α < π := by
  cases (club_closedC hπ α hη₀).1 η₀ hη₀ with
  | intro ρ hρ =>
    exact lt_of_le_of_lt (Psi_le_of (hB.mono_base (Or.inl hρ.1.1)) hρ.2.2 hρ.1.2) hρ.2.2

/-- `Ψ_π(α) < π` なら `Ψ_π(α)` は加法的主数 -/
theorem Psi_principal_of_lt {π α : Ordinal.{u}} (hπ : R π) (h : Psi π α < π) :
    IsPrincipal (Psi π α) := by
  have hs := Psi_spec h
  have hpos : 0 < Psi π α := by
    rcases hs.1 with ⟨_, h2⟩ | ⟨ζ, _, _, h3⟩ | ⟨m, δ, _, _, _, _, h3, _⟩
    · exact h2
    · exact lt_of_le_of_lt (zero_le _) h3
    · exact lt_of_le_of_lt (zero_le _) h3
  refine And.intro (ne_of_gt hpos) ?_
  intro a b ha hb
  exact hs.2 _ (C_add (C_lt ha) (C_lt hb))
    (hπ.2.add_lt (lt_trans _ _ _ ha h) (lt_trans _ _ _ hb h))

/-! ### `Ψ_{Ω_0}(0) = 1` -/

theorem C_zero_one_lt {x : Ordinal.{u}} (h : C 0 (succ 0) x) (hx : x < Om 0) : x = 0 := by
  cases h with
  | intro n hn =>
    unfold Cn at hn
    induction hn with
    | lt _ γ hγ => exact (le_zero_iff γ).mp (le_of_lt_succ hγ)
    | kc _ m =>
      cases m with
      | zero => rfl
      | succ m =>
        have hn : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
        exact absurd (Om_zero_lt_K hn) (lt_asymm hx)
    | add _ y z _ _ ihy ihz =>
      have hy : y < Om 0 := lt_of_le_of_lt (le_add y z) hx
      have hz : z < Om 0 := lt_of_le_of_lt (right_le_add y z) hx
      rw [ihy hy, ihz hz, add_zero]
    | om _ y hΛ _ _ =>
      exact absurd hx (not_lt_of_le (Om_le_Om (zero_le y) hΛ))
    | xi _ _ _ hα _ _ _ => exact absurd hα (not_lt_zero _)
    | psi _ _ _ hα _ _ _ _ _ _ _ => exact absurd hα (not_lt_zero _)

theorem one_lt_Om_zero : succ (0 : Ordinal.{u}) < Om 0 :=
  lt_trans _ _ _ (ordNat_lt_omega 1) Om_zero_R.1

/-- `Ψ_{Ω_0}(0) = 1` -/
theorem Psi_Om_zero_zero : Psi (Om (0 : Ordinal.{u})) 0 = succ 0 := by
  apply le_antisymm
  · apply Psi_le_of (Or.inl ⟨rfl, lt_succ_self 0⟩) one_lt_Om_zero
    intro x hx hxπ
    rw [C_zero_one_lt hx hxπ]
    exact lt_succ_self 0
  · apply succ_le_of_lt
    apply lt_of_le_of_ne (zero_le _)
    intro e
    have hlt : Psi (Om (0 : Ordinal.{u})) 0 < Om 0 := by
      rw [← e]; exact Om_pos Λ_pos
    rcases (Psi_spec hlt).1 with ⟨_, h2⟩ | ⟨ζ, hζ, h2, _⟩ | ⟨m, δ, hδ, _, _, _, _⟩
    · rw [← e] at h2; exact lt_irrefl _ h2
    · exact absurd (Om_inj Λ_pos hζ h2) (succ_ne_zero ζ).symm
    · exact absurd hδ (not_lt_zero δ)

/-- `α > 0` なら `1 ∈ C(α, β)` -/
theorem C_one {α β : Ordinal.{u}} (hα : 0 < α) : C α β (succ 0) := by
  have hlt : Psi (Om (0 : Ordinal.{u})) 0 < Om 0 := by
    rw [Psi_Om_zero_zero]; exact one_lt_Om_zero
  have h := C_Psi (β := β) hα isReg_Om_zero hlt (C_zero 0 _) (C_Om_zero α β) (C_zero α β)
  rw [Psi_Om_zero_zero] at h
  exact h

/-- `1 < β` なら `1 ∈ C(α, β)` -/
theorem C_one_of_lt {α β : Ordinal.{u}} (hβ : succ 0 < β) : C α β (succ 0) := C_lt hβ

end

end OCF.Mahlo
