import Mahlo.Compare

/-! `C(γ, δ)` の元の分解と、生成子の値の一意性。

* `Cn_cnf`：`z ∈ C(γ, δ)` の Cantor 標準形の項は、同じ段階で `C(γ, δ)` に入る。
* `Cn_gen`・`C_gen`：加法的主数 `z ∈ C(γ, δ)` で `z ≥ δ` のものは、本物の生成子の値
  （`K_m`、`Ω_w`（`w < Ω_w`）、`Ξ_m(x) < K_m`、正規な引数の `Ψ_π(β) < π`）で、引数は前の段階で入る。
* `GenRep_Om`・`GenRep_Xi`・`GenRep_Psi`：生成子の値の表示は引数まで一意。
* `base_Om_zero_iff`・`base_Om_succ_iff`・`base_Xi_iff`：崩壊先ごとの底の条件の形。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen

noncomputable section

/-- `0` か加法的主数の Cantor 標準形は、自分自身だけからなる -/
theorem cnf_mem_eq_of_principal_or_zero {z : Ordinal.{u}} (hz : z = 0 ∨ IsPrincipal z)
    {l : List Ordinal.{u}} (h : CNF z l) {p : Ordinal.{u}} (hp : p ∈ l) : p = z := by
  cases hz with
  | inl h0 =>
    rw [h0] at h
    rw [cnf_unique h cnf_zero] at hp
    exact absurd hp List.not_mem_nil
  | inr hP =>
    rw [cnf_of_principal hP h] at hp
    exact List.mem_singleton.mp hp

variable [Setting.{u}]

theorem C_of_cnf {γ δ z : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF z l)
    (hl : ∀ p, p ∈ l → C γ δ p) : C γ δ z := by
  rw [h.eq]
  clear h
  induction l with
  | nil => exact C_zero γ δ
  | cons a l ih =>
    rw [listSum_cons]
    exact C_add (hl a List.mem_cons_self) (ih (fun p hp => hl p (List.mem_cons_of_mem a hp)))

theorem K_principal_or_zero (m : Nat) : K.{u} m = 0 ∨ IsPrincipal (K m) := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m => exact Or.inr (R_K (Nat.succ_le_succ (Nat.zero_le m))).2.isPrincipal

theorem Xi_principal_or_zero (m : Nat) (x : Ordinal.{u}) : Xi m x = 0 ∨ IsPrincipal (Xi m x) := by
  by_cases h : Xi m x < K m
  · exact Or.inr (xiGood_of_lt h).R.2.isPrincipal
  · rw [Xi_eq_K_of_not_lt h]; exact K_principal_or_zero m

/-- Cantor 標準形の項 -/
theorem Cn_cnf {γ δ : Ordinal.{u}} : ∀ {n : Nat} {z : Ordinal.{u}}, Cn γ δ n z →
    ∀ {l : List Ordinal.{u}}, CNF z l → ∀ p, p ∈ l → Cn γ δ n p := by
  intro n z h
  unfold Cn at h ⊢
  induction h with
  | lt n w hw =>
    intro l hl p hp
    exact StageC.lt n p (lt_of_le_of_lt (hl.le hp) hw)
  | kc n m =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (K_principal_or_zero m) hl hp]
    exact StageC.kc n m
  | add n x y _ _ ihx ihy =>
    intro l hl p hp
    cases cnf_exists x with
    | intro lx hx =>
      cases cnf_exists y with
      | intro ly hy =>
        cases cnf_add hx hy with
        | intro l' hl' =>
          rw [cnf_unique hl hl'.1] at hp
          cases hl'.2 p hp with
          | inl h => exact Cn_succ (ihx hx p h)
          | inr h => exact Cn_succ (ihy hy p h)
  | om n x hΛ hx _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Or.inr (Om_principal hΛ)) hl hp]
    exact StageC.om n x hΛ hx
  | xi n m x hα hc hx _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Xi_principal_or_zero m x) hl hp]
    exact StageC.xi n m x hα hc hx
  | psi n π β hβ hπ hlt hnorm hπC hβC _ _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Or.inr (Psi_principal_of_lt hπ.1 hlt)) hl hp]
    exact StageC.psi n π β hβ hπ hlt hnorm hπC hβC

theorem C_cnf {γ δ z : Ordinal.{u}} (h : C γ δ z) {l : List Ordinal.{u}} (hl : CNF z l)
    {p : Ordinal.{u}} (hp : p ∈ l) : C γ δ p := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_cnf hn hl p hp)

/-- `z ∈ C(γ, δ)` ⟺ `z` の Cantor 標準形の項が全て `C(γ, δ)` に入る -/
theorem C_iff_cnf {γ δ z : Ordinal.{u}} {l : List Ordinal.{u}} (hl : CNF z l) :
    C γ δ z ↔ ∀ p, p ∈ l → C γ δ p :=
  Iff.intro (fun h _ hp => C_cnf h hl hp) (C_of_cnf hl)

/-! ### 生成子への分解 -/

/-- 本物の生成子による表示（引数は `S` に入る） -/
def GenRep (S : Ordinal.{u} → Prop) (γ z : Ordinal.{u}) : Prop :=
  (∃ m, z = K m) ∨
    (∃ w, S w ∧ w < Λ ∧ w < Om w ∧ z = Om w) ∨
    (∃ m x, S x ∧ x < γ ∧ x ≤ capK m ∧ Xi m x < K m ∧ z = Xi m x) ∨
    (∃ π β, S π ∧ S β ∧ β < γ ∧ IsReg π ∧ Psi π β < π ∧ C β (Psi π β) β ∧ z = Psi π β)

theorem GenRep.mono {S T : Ordinal.{u} → Prop} (hST : ∀ x, S x → T x) {γ z : Ordinal.{u}}
    (h : GenRep S γ z) : GenRep T γ z := by
  rcases h with h | ⟨w, hw, h⟩ | ⟨m, x, hx, h⟩ | ⟨π, β, hπ, hβ, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨w, hST w hw, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, x, hST x hx, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨π, β, hST π hπ, hST β hβ, h⟩))

/-- `n` より前の段階で `C(γ, δ)` に入る -/
def Below (γ δ : Ordinal.{u}) (n : Nat) (x : Ordinal.{u}) : Prop := ∃ k, k < n ∧ Cn γ δ k x

theorem Below.mono {γ δ : Ordinal.{u}} {n m : Nat} (h : n ≤ m) {x : Ordinal.{u}}
    (hx : Below γ δ n x) : Below γ δ m x := by
  cases hx with
  | intro k hk => exact Exists.intro k (And.intro (Nat.lt_of_lt_of_le hk.1 h) hk.2)

/-- 加法的主数 `z ∈ C_n(γ, δ)` で `δ ≤ z` なら、`n` より前の段階の引数による本物の生成子の表示がある -/
theorem Cn_gen {γ δ : Ordinal.{u}} : ∀ {n : Nat} {z : Ordinal.{u}}, Cn γ δ n z →
    IsPrincipal z → δ ≤ z → GenRep (Below γ δ n) γ z := by
  intro n z h
  unfold Cn at h
  induction h with
  | lt n w hw => intro _ hle; exact absurd hw (not_lt_of_le hle)
  | kc n m => intro _ _; exact Or.inl ⟨m, rfl⟩
  | add n x y _ _ ihx ihy =>
    intro hP hle
    cases hP.add_cases with
    | inl h =>
      rw [h.1] at hP hle ⊢
      exact (ihx hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
    | inr h =>
      rw [h] at hP hle ⊢
      exact (ihy hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
  | om n x hΛ hx ih =>
    intro hP hle
    by_cases hlt : x < Om x
    · exact Or.inr (Or.inl ⟨x, ⟨n, Nat.lt_succ_self n, hx⟩, hΛ, hlt, rfl⟩)
    · have he : Om x = x := le_antisymm (le_of_not_lt hlt) (le_Om hΛ)
      rw [he] at hP hle ⊢
      exact (ih hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
  | xi n m x hα hc hx _ =>
    intro _ _
    show GenRep _ _ (Xi m x)
    by_cases hlt : Xi m x < K m
    · exact Or.inr (Or.inr (Or.inl ⟨m, x, ⟨n, Nat.lt_succ_self n, hx⟩, hα, hc, hlt, rfl⟩))
    · rw [Xi_eq_K_of_not_lt hlt]
      exact Or.inl ⟨m, rfl⟩
  | psi n π β hβ hπ hlt hnorm hπC hβC _ _ =>
    intro _ _
    show GenRep _ _ (Psi π β)
    exact Or.inr (Or.inr (Or.inr ⟨π, β, ⟨n, Nat.lt_succ_self n, hπC⟩,
      ⟨n, Nat.lt_succ_self n, hβC⟩, hβ, hπ, hlt, (stages_C _ _ _).mp hnorm, rfl⟩))

theorem C_gen {γ δ z : Ordinal.{u}} (h : C γ δ z) (hP : IsPrincipal z) (hle : δ ≤ z) :
    GenRep (C γ δ) γ z := by
  cases h with
  | intro n hn =>
    exact (Cn_gen hn hP hle).mono (fun x hx => by
      cases hx with
      | intro k hk => exact Exists.intro k hk.2)

/-! ### 生成子の値が互いに異なること -/

theorem Om_ne_K {w : Ordinal.{u}} {m : Nat} (hΛ : w < Λ) (hlt : w < Om w) : Om w ≠ K m := by
  intro e
  cases m with
  | zero => exact absurd e (ne_of_gt (Om_pos hΛ))
  | succ m =>
    have hK := Om_K (Nat.succ_le_succ (Nat.zero_le m))
    rw [← hK] at e
    have hw := Om_inj hΛ (K_lt_Λ _) e
    rw [hw, hK] at hlt
    exact lt_irrefl _ hlt

theorem Om_ne_Xi {w x : Ordinal.{u}} {m : Nat} (hΛ : w < Λ) (hlt : w < Om w)
    (hX : Xi m x < K m) : Om w ≠ Xi m x := by
  intro e
  have hf := (xiGood_of_lt hX).fixed
  rw [← hf] at e
  have hw := Om_inj hΛ (lt_trans _ _ _ hX (K_lt_Λ m)) e
  rw [hw, hf] at hlt
  exact lt_irrefl _ hlt

theorem Om_ne_Psi {w π β : Ordinal.{u}} (hΛ : w < Λ) (hlt : w < Om w) (hψ : Psi π β < π) :
    Om w ≠ Psi π β := by
  intro e
  have sp := Psi_spec hψ
  have hw : w < Psi π β := by rw [← e]; exact hlt
  have h := sp.2 _ (C_Om hΛ (C_lt hw)) (by rw [e]; exact hψ)
  rw [e] at h
  exact lt_irrefl _ h

theorem Xi_ne_K {m m' : Nat} {x : Ordinal.{u}} (hX : Xi m x < K m) : Xi m x ≠ K m' := by
  intro e
  have h1 := (xiGood_of_lt hX).gt
  rw [e] at h1 hX
  have a := K_lt_iff.mp h1
  have b := K_lt_iff.mp hX
  omega

theorem Psi_ne_K {π β : Ordinal.{u}} {m : Nat} (hψ : Psi π β < π) : Psi π β ≠ K m := by
  intro e
  have h := (Psi_spec hψ).2 _ (C_K β _ m) (by rw [← e]; exact hψ)
  rw [e] at h
  exact lt_irrefl _ h

theorem Xi_ne_Psi {m : Nat} {x π β : Ordinal.{u}} (hX : Xi m x < K m) (hc : x ≤ capK m)
    (hψ : Psi π β < π) :
    Psi π β ≠ Xi m x :=
  Psi_ne_regTarget hψ (Or.inr (Or.inr ⟨m, x, hc, rfl, hX⟩))

/-! ### 表示の一意性 -/

theorem GenRep_Om {S : Ordinal.{u} → Prop} {γ w : Ordinal.{u}} (h : GenRep S γ (Om w))
    (hΛ : w < Λ) (hlt : w < Om w) : S w := by
  rcases h with ⟨m, h⟩ | ⟨w', hw', hΛ', _, h⟩ | ⟨m, x, _, _, _, hX, h⟩ |
      ⟨π, β, _, _, _, _, hψ, _, h⟩
  · exact absurd h (Om_ne_K hΛ hlt)
  · rw [Om_inj hΛ hΛ' h]; exact hw'
  · exact absurd h (Om_ne_Xi hΛ hlt hX)
  · exact absurd h (Om_ne_Psi hΛ hlt hψ)

theorem GenRep_Xi {S : Ordinal.{u} → Prop} {γ x : Ordinal.{u}} {m : Nat}
    (h : GenRep S γ (Xi m x)) (hX : Xi m x < K m) (hc : x ≤ capK m) : S x ∧ x < γ := by
  rcases h with ⟨m', h⟩ | ⟨w, _, hΛ, hlt, h⟩ | ⟨m', x', hx', hxγ, hc', hX', h⟩ |
      ⟨π, β, _, _, _, _, hψ, _, h⟩
  · exact absurd h (Xi_ne_K hX)
  · exact absurd h.symm (Om_ne_Xi hΛ hlt hX)
  · rw [(Xi_inj' hX hX' hc hc' h).2]; exact And.intro hx' hxγ
  · exact absurd h.symm (Xi_ne_Psi hX hc hψ)

theorem GenRep_Psi {S : Ordinal.{u} → Prop} {γ π β : Ordinal.{u}}
    (h : GenRep S γ (Psi π β)) (hψ : Psi π β < π) (hn : C β (Psi π β) β) :
    S π ∧ S β ∧ β < γ := by
  rcases h with ⟨m, h⟩ | ⟨w, _, hΛ, hlt, h⟩ | ⟨m, x, _, _, hc, hX, h⟩ |
      ⟨π', β', hπ', hβ', hβγ, _, hψ', hn', h⟩
  · exact absurd h (Psi_ne_K hψ)
  · exact absurd h.symm (Om_ne_Psi hΛ hlt hψ)
  · exact absurd h (Xi_ne_Psi hX hc hψ)
  · have e := Psi_inj hψ hψ' hn hn' h
    rw [e.1, e.2]
    exact ⟨hπ', hβ', hβγ⟩

/-! ### 底の条件の形 -/

theorem base_Om_zero_iff {η : Ordinal.{u}} : Base (Om 0) η ↔ 0 < η := by
  apply Iff.intro
  · rintro (⟨_, h⟩ | ⟨ζ, hζ, e, _⟩ | ⟨m, δ, _, e, hX, _, _⟩)
    · exact h
    · exact absurd e (Om_zero_ne_Om_succ hζ)
    · have hX' : Xi m δ < K m := by rw [← e]; exact hX
      exact absurd e.symm (Xi_ne_Om_zero hX')
  · intro h
    exact Or.inl ⟨rfl, h⟩

theorem base_Om_succ_iff {ζ η : Ordinal.{u}} (hζ : succ ζ < Λ) :
    Base (Om (succ ζ)) η ↔ Om ζ < η := by
  apply Iff.intro
  · rintro (⟨e, _⟩ | ⟨ζ', hζ', e, h⟩ | ⟨m, δ, _, e, hX, _, _⟩)
    · exact absurd e.symm (Om_zero_ne_Om_succ hζ)
    · have hz := succ_inj (Om_inj hζ hζ' e)
      rw [hz]
      exact h
    · have hX' : Xi m δ < K m := by rw [← e]; exact hX
      exact absurd e.symm (Xi_ne_Om_succ hX' hζ)
  · intro h
    exact Or.inr (Or.inl ⟨ζ, hζ, rfl, h⟩)

theorem base_Xi_iff {m : Nat} {δ η : Ordinal.{u}} (hX : Xi m δ < K m) (hc : δ ≤ capK m) :
    Base (Xi m δ) η ↔ K (m - 1) < η ∧ C δ η δ := by
  apply Iff.intro
  · rintro (⟨e, _⟩ | ⟨ζ, hζ, e, _⟩ | ⟨m', δ', hc', e, hX', h3, h4⟩)
    · exact absurd e (Xi_ne_Om_zero hX)
    · exact absurd e (Xi_ne_Om_succ hX hζ)
    · have hX'' : Xi m' δ' < K m' := by rw [← e]; exact hX'
      obtain ⟨rfl, rfl⟩ := Xi_inj' hX hX'' hc hc' e
      exact ⟨h3, h4⟩
  · intro h
    exact Or.inr (Or.inr ⟨m, δ, hc, rfl, hX, h.1, h.2⟩)

/-! ### `Ψ` の値の位置 -/

theorem Psi_pos {π α : Ordinal.{u}} (h : Psi π α < π) : 0 < Psi π α :=
  (Psi_principal_of_lt (regTarget_of_Psi_lt h).isReg.1 h).pos

/-- `Ω_ζ < Ψ_{Ω_{ζ+1}}(α) < Ω_{ζ+1}` -/
theorem Psi_Om_succ_gt {ζ : Ordinal.{u}} (hζ : succ ζ < Λ) (α : Ordinal.{u}) :
    Om ζ < Psi (Om (succ ζ)) α :=
  (base_Om_succ_iff hζ).mp (Psi_base (Psi_Om_succ_lt hζ α))

/-- `Ψ_{Ω_{ζ+1}}(α)` は `Ω` の不動点でない -/
theorem Psi_Om_succ_lt_Om {ζ : Ordinal.{u}} (hζ : succ ζ < Λ) (α : Ordinal.{u}) :
    Psi (Om (succ ζ)) α < Om (Psi (Om (succ ζ)) α) := by
  have hlt := Psi_Om_succ_lt hζ α
  have hΛ : Psi (Om (succ ζ)) α < Λ := lt_trans _ _ _ hlt (Om_lt_Λ hζ)
  apply lt_of_le_of_ne (le_Om hΛ)
  intro e
  have hc : closure R (Psi (Om (succ ζ)) α) := by rw [e]; exact cardSet_Om hΛ
  obtain ⟨y, hy, ey⟩ := Om_surj hc hΛ
  have h1 := Psi_Om_succ_gt hζ α
  rw [← ey] at h1 hlt
  have hζy := (Om_lt_Om_iff (lt_trans _ _ _ (lt_succ_self ζ) hζ) hy).mp h1
  have hys := (Om_lt_Om_iff hy hζ).mp hlt
  exact absurd (lt_of_lt_of_le hζy (le_of_lt_succ hys)) (lt_irrefl _)

theorem Psi_Om_zero_lt_Om (α : Ordinal.{u}) :
    Psi (Om 0) α < Om (Psi (Om 0) α) := by
  have hlt := Psi_Om_zero_lt α
  have hΛ : Psi (Om (0 : Ordinal.{u})) α < Λ := lt_trans _ _ _ hlt (Om_lt_Λ Λ_pos)
  exact lt_of_lt_of_le hlt (Om_le_Om (zero_le _) hΛ)

end

end OCF.Mahlo
