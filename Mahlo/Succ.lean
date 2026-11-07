import Mahlo.NF

/-! 後続基数への崩壊の基本列：`Ψ_π(β+1)` の基本列は `Ψ_π(β)·(n+1)`。

崩壊先 `π` が `Ω_0` または `Ω_{ζ+1}` のとき、`β` が正規（`β ∈ C(β, Ψ_π(β))`）なら

* `Ψ_π(β)·(n+1) < Ψ_π(β+1)`（`iterAdd`）、
* `Ψ_π(β+1)` 未満の順序数はある `Ψ_π(β)·(n+1)` 未満

（`Psi_succ_fs`）。つまり `Ψ_π(β+1) = Ψ_π(β)·ω`。また `β+1` が正規なら `β` も正規
（`normal_of_normal_succ`）。

記法系では、`Ψ_π(b+1)` が標準形（`π = Ω_0` か `Ω_{c'+1}`）なら、`fsTerm π b n`
（`Ψ_π(b)` を `n+1` 個足した項）は標準形で、狭義増加し、`Ψ_π(b+1)` に収束する（`fs_psi_succ`）。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen MahloOCF

noncomputable section

/-- `x` を `n` 個足したもの -/
def iterAdd (x : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => iterAdd x n + x

theorem iterAdd_lt {p x : Ordinal.{u}} (hp : IsPrincipal p) (hx : x < p) :
    ∀ n, iterAdd x n < p
  | 0 => hp.pos
  | n + 1 => hp.2 _ _ (iterAdd_lt hp hx n) hx

theorem iterAdd_lt_succ {x : Ordinal.{u}} (hx : 0 < x) (n : Nat) :
    iterAdd x n < iterAdd x (n + 1) := by
  show iterAdd x n < iterAdd x n + x
  have h := add_lt_add_right (iterAdd x n) hx
  rw [add_zero] at h
  exact h

theorem iterAdd_add (x : Ordinal.{u}) (m : Nat) : ∀ n, iterAdd x m + iterAdd x n = iterAdd x (m + n)
  | 0 => add_zero _
  | n + 1 => by
    show iterAdd x m + (iterAdd x n + x) = iterAdd x (m + n) + x
    rw [← add_assoc, iterAdd_add x m n]

theorem iterAdd_comm (x : Ordinal.{u}) : ∀ n, x + iterAdd x n = iterAdd x n + x
  | 0 => by show x + 0 = 0 + x; rw [add_zero, zero_add]
  | n + 1 => by
    show x + (iterAdd x n + x) = (iterAdd x n + x) + x
    rw [← add_assoc, iterAdd_comm x n]

theorem le_iterAdd_one (x : Ordinal.{u}) : x ≤ iterAdd x 1 := by
  show x ≤ iterAdd x 0 + x
  exact right_le_add _ _

/-- 狭義増加の列の上限は、各項を足し合わせて閉じていれば加法的主数 -/
theorem add_lt_add_of_lt {u₁ v₁ a b : Ordinal.{u}} (h1 : u₁ < a) (h2 : v₁ < b) :
    u₁ + v₁ < a + b :=
  lt_of_lt_of_le (add_lt_add_right u₁ h2) (add_mono_left (Or.inl h1) b)

variable [Setting.{u}]

theorem C_iterAdd {α β x : Ordinal.{u}} (h : C α β x) : ∀ n, C α β (iterAdd x n)
  | 0 => C_zero α β
  | n + 1 => C_add (C_iterAdd h n) h

/-- `x + 1 ∈ C(γ, δ)` なら `x ∈ C(γ, δ)` -/
theorem C_of_succ {γ δ x : Ordinal.{u}} (h : C γ δ (succ x)) : C γ δ x := by
  obtain ⟨lx, hx⟩ := cnf_exists x
  have hc : CNF (succ x) (lx ++ [succ 0]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      cases List.mem_append.mp hp with
      | inl h => exact hx.1 p h
      | inr h => rw [List.mem_singleton.mp h]; exact isPrincipal_one
    · apply List.pairwise_append.mpr
      refine ⟨hx.2.1, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]
      exact succ_le_of_lt (hx.1 a ha).pos
    · rw [listSum_append, listSum_cons, listSum_nil, add_zero, ← hx.eq, add_one_eq_succ]
  exact C_of_cnf hx (fun p hp => C_cnf h hc (List.mem_append_left _ hp))

/-- `b ∉ C(b, η)` なら `C(b+1, η) ⊆ C(b, η)` -/
theorem C_succ_sub {b η : Ordinal.{u}} (hb : ¬ C b η b) :
    ∀ n x, Cn (succ b) η n x → C b η x := by
  intro n x h
  unfold Cn at h
  induction h with
  | lt _ γ hγ => exact C_lt hγ
  | kc _ m => exact C_K _ _ m
  | add _ x y _ _ ihx ihy => exact C_add ihx ihy
  | om _ x hΛ _ ih => exact C_Om hΛ ih
  | xi _ m x hα hc _ ih =>
    cases (lt_succ_iff_le x b).mp hα with
    | inl hlt => exact C_Xi m hlt hc ih
    | inr e => rw [e] at ih; exact absurd ih hb
  | psi _ π δ hα hπ hlt hnorm _ _ ihπ ihδ =>
    cases (lt_succ_iff_le δ b).mp hα with
    | inl h' => exact C_Psi h' hπ hlt ((stages_C _ _ _).mp hnorm) ihπ ihδ
    | inr e => rw [e] at ihδ; exact absurd ihδ hb

/-- `Ψ_π(b) < π` で `b + 1` が正規なら `b` も正規 -/
theorem normal_of_normal_succ {π b : Ordinal.{u}} (hact : Psi π b < π)
    (h : C (succ b) (Psi π (succ b)) (succ b)) : C b (Psi π b) b := by
  apply Classical.byContradiction
  intro hb
  have hsub := C_succ_sub hb
  -- `Ψ_π(b+1) ≤ Ψ_π(b)`
  have hle : Psi π (succ b) ≤ Psi π b := by
    apply Psi_le_of ((Psi_spec hact).1.mono_arg (Or.inl (lt_succ_self b))) hact
    intro x hx hxπ
    cases hx with
    | intro n hn => exact (Psi_spec hact).2 x (hsub n x hn) hxπ
  have h' : C (succ b) (Psi π b) (succ b) := C_mono_base hle h
  cases C_of_succ h' with
  | intro n hn => exact hb (hsub n b hn)

/-- 後続基数（`Ω_0` か `Ω_{ζ+1}`）より小さい基数は `Ω_ζ` 以下 -/
theorem card_le_of_lt_target {π ζ κ : Ordinal.{u}} (hζ : succ ζ < Λ) (hπ : π = Om (succ ζ))
    (hκ : closure R κ) (hlt : κ < π) : κ ≤ Om ζ := by
  have hκΛ : κ < Λ := lt_trans _ _ _ hlt (by rw [hπ]; exact Om_lt_Λ hζ)
  obtain ⟨y, hy, ey⟩ := Om_surj hκ hκΛ
  rw [hπ, ← ey] at hlt
  rw [← ey]
  exact Om_le_Om (le_of_lt_succ ((Om_lt_Om_iff hy hζ).mp hlt)) (lt_trans _ _ _ (lt_succ_self ζ) hζ)

theorem not_card_lt_Om_zero {κ : Ordinal.{u}} (hκ : closure R κ) : ¬ κ < Om 0 := by
  intro hlt
  have hκΛ : κ < Λ := lt_trans _ _ _ hlt (Om_lt_Λ Λ_pos)
  obtain ⟨y, hy, ey⟩ := Om_surj hκ hκΛ
  rw [← ey] at hlt
  exact not_lt_of_le (Om_le_Om (zero_le y) hy) hlt

/-- 基数でも `0` でもない値は `K_m`・`Ξ`・`Ω` から作れない：`K_m` は `0` か基数 -/
theorem K_zero_or_card (m : Nat) : K.{u} m = 0 ∨ closure R (K m) := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m => exact Or.inr (subset_closure (R_K (Nat.succ_le_succ (Nat.zero_le m))))

theorem Xi_zero_or_card (m : Nat) (x : Ordinal.{u}) : Xi m x = 0 ∨ closure R (Xi m x) := by
  by_cases h : Xi m x < K m
  · exact Or.inr (subset_closure (xiGood_of_lt h).R)
  · rw [Xi_eq_K_of_not_lt h]; exact K_zero_or_card m

/-- 後続基数への崩壊の基本列 -/
theorem Psi_succ_fs {π b : Ordinal.{u}}
    (hπ : π = Om 0 ∨ ∃ ζ, succ ζ < Λ ∧ π = Om (succ ζ)) (hn : C b (Psi π b) b) :
    (∀ n, iterAdd (Psi π b) (n + 1) < Psi π (succ b)) ∧
      (∀ x, x < Psi π (succ b) → ∃ n, x < iterAdd (Psi π b) (n + 1)) := by
  have hRT : RegTarget π := by
    rcases hπ with h | ⟨ζ, hζ, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨ζ, hζ, h⟩)
  have hR := hRT.isReg
  have hact : ∀ γ, Psi π γ < π := by
    intro γ
    rcases hπ with h | ⟨ζ, hζ, h⟩
    · rw [h]; exact Psi_Om_zero_lt γ
    · rw [h]; exact Psi_Om_succ_lt hζ γ
  have hψ := hact b
  have hψ' := hact (succ b)
  have hψ0 : 0 < Psi π b := Psi_pos hψ
  have hP := hR.1.2.isPrincipal
  -- 前半
  have hfirst : ∀ n, iterAdd (Psi π b) (n + 1) < Psi π (succ b) := by
    intro n
    have hle := Psi_mono (Or.inl (lt_succ_self b)) hψ hψ'
    have hC : C (succ b) (Psi π (succ b)) (Psi π b) :=
      C_Psi (lt_succ_self b) hR hψ hn (Psi_C_pi hψ')
        (C_mono_arg (Or.inl (lt_succ_self b)) (C_mono_base hle hn))
    exact (Psi_spec hψ').2 _ (C_iterAdd hC (n + 1)) (iterAdd_lt hP hψ (n + 1))
  refine And.intro hfirst ?_
  -- 後半：`s = sup_n Ψ_π(b)·(n+1)` で `Ψ_π(b+1) ≤ s`
  intro x hx
  apply Classical.byContradiction
  intro hno
  have hge : ∀ n, iterAdd (Psi π b) (n + 1) ≤ x := fun n =>
    le_of_not_lt (fun h => hno ⟨n, h⟩)
  let f : Nat → Ordinal.{u} := fun n => iterAdd (Psi π b) (n + 1)
  have hf : ∀ n, f n < f (n + 1) := fun n => iterAdd_lt_succ hψ0 (n + 1)
  let s := omegaSup f
  have hsπ : s < π := omegaSup_lt hR.1 (fun n => iterAdd_lt hP hψ (n + 1))
  have hψs : Psi π b < s := lt_of_le_of_lt (le_iterAdd_one _) (lt_omegaSup hf 0)
  have hs0 : 0 < s := lt_trans _ _ _ hψ0 hψs
  have hsP : ∀ y z, y < s → z < s → y + z < s := by
    intro y z hy hz
    obtain ⟨i, hi⟩ := (lt_omegaSup_iff y).mp hy
    obtain ⟨j, hj⟩ := (lt_omegaSup_iff z).mp hz
    have h := add_lt_add_of_lt hi hj
    have e : f i + f j = f (i + j + 1) := by
      show iterAdd _ (i + 1) + iterAdd _ (j + 1) = iterAdd _ (i + j + 1 + 1)
      rw [iterAdd_add]
      congr 1
      omega
    rw [e] at h
    exact lt_trans _ _ _ h (lt_omegaSup hf _)
  -- `Ψ_π(b)` 未満の小さな値
  have hsmall : ∀ κ, closure R κ → κ < π → κ < s := by
    intro κ hκ hκπ
    rcases hπ with h | ⟨ζ, hζ, h⟩
    · rw [h] at hκπ; exact absurd hκπ (not_card_lt_Om_zero hκ)
    · have hle := card_le_of_lt_target hζ h hκ hκπ
      have hgt : Om ζ < Psi π b := by rw [h]; exact Psi_Om_succ_gt hζ b
      exact lt_of_le_of_lt hle (lt_trans _ _ _ hgt hψs)
  have hcl : ∀ y, C (succ b) s y → y < π → y < s := by
    intro y hy
    cases hy with
    | intro n hn =>
      unfold Cn at hn
      induction hn with
      | lt _ γ hγ => intro _; exact hγ
      | kc _ m =>
        intro hlt
        cases K_zero_or_card.{u} m with
        | inl h0 => rw [h0]; exact hs0
        | inr hc => exact hsmall _ hc hlt
      | add _ y z _ _ ihy ihz =>
        intro hlt
        exact hsP _ _ (ihy (lt_of_le_of_lt (le_add y z) hlt))
          (ihz (lt_of_le_of_lt (right_le_add y z) hlt))
      | om _ y hΛ _ _ =>
        intro hlt
        exact hsmall _ (cardSet_Om hΛ) hlt
      | xi _ m y _ _ _ =>
        intro hlt
        cases Xi_zero_or_card m y with
        | inl h0 => show Xi m y < s; rw [h0]; exact hs0
        | inr hc => exact hsmall _ hc hlt
      | psi _ σ δ hδ hσ hlt hnorm _ _ _ _ =>
        intro hvπ
        show Psi σ δ < s
        rcases lt_total σ π with hσπ | hσπ | hσπ
        · exact lt_trans _ _ _ hlt (hsmall _ (subset_closure hσ.1) hσπ)
        · rw [hσπ] at hlt ⊢
          have hδb : δ ≤ b := (lt_succ_iff_le δ b).mp hδ
          exact lt_of_le_of_lt (Psi_mono hδb hlt hψ) hψs
        · have hnB : ¬ Base π (Psi σ δ) := fun hB => sep hlt hσπ (Or.inl hvπ) hB
          rcases hπ with h | ⟨ζ, hζ, h⟩
          · rw [h, base_Om_zero_iff] at hnB
            have e : Psi σ δ = 0 := (le_zero_iff _).mp (le_of_not_lt hnB)
            rw [e]; exact hs0
          · rw [h, base_Om_succ_iff hζ] at hnB
            have hgt : Om ζ < Psi π b := by rw [h]; exact Psi_Om_succ_gt hζ b
            exact lt_of_le_of_lt (le_of_not_lt hnB) (lt_trans _ _ _ hgt hψs)
  have hB : BaseA (succ b) π s := by
    rcases hπ with h | ⟨ζ, hζ, h⟩
    · exact Or.inl ⟨h, hs0⟩
    · have hgt : Om ζ < Psi π b := by rw [h]; exact Psi_Om_succ_gt hζ b
      exact Or.inr (Or.inl ⟨ζ, hζ, h, lt_trans _ _ _ hgt hψs⟩)
  have hle : Psi π (succ b) ≤ s := Psi_le_of hB hsπ hcl
  have hsx : s ≤ x := (supLt_le_iff _ _ _).mpr (fun ζ _ => hge (natOf ζ))
  exact absurd (lt_of_lt_of_le hx (le_trans hle hsx)) (lt_irrefl _)

/-! ### 記法系での基本列 -/

/-- `Ψ_π(b)` を `n + 1` 個足した項 -/
def fsTerm (pi b : Tm) (n : Nat) : Tm := ofSummands (List.replicate (n + 1) (.Psi pi b))

theorem val_fsTerm (pi b : Tm) (n : Nat) :
    val.{u} (fsTerm pi b n) = iterAdd (val (Tm.Psi pi b)) (n + 1) := by
  rw [fsTerm, val_ofSummands, List.map_replicate]
  induction n with
  | zero =>
    show listSum [_] = iterAdd _ 0 + _
    rw [listSum_cons, listSum_nil, add_zero]
    exact (zero_add _).symm
  | succ n ih =>
    rw [List.replicate_succ, listSum_cons, ih]
    show _ + (iterAdd _ n + _) = (iterAdd _ n + _) + _
    rw [← add_assoc]
    congr 1
    exact iterAdd_comm _ n

theorem good_fsTerm {pi b : Tm} (h : Good.{u} (.Psi pi b)) :
    ∀ n, Good.{u} (fsTerm pi b n)
  | 0 => h
  | n + 1 => by
    show Good (ofSummands (Tm.Psi pi b :: List.replicate (n + 1) (Tm.Psi pi b)))
    have ih := good_fsTerm h n
    show Good (Tm.plus (Tm.Psi pi b) (ofSummands (List.replicate (n + 1) (Tm.Psi pi b))))
    refine Good.plus _ _ h ih rfl ?_ ?_
    · exact ofSummands_ne_zero _ (by simp) (fun s hs => by
        rw [List.eq_of_mem_replicate hs]; rfl)
    · intro h' hh
      rw [summands_ofSummands _ (fun s hs => by rw [List.eq_of_mem_replicate hs]; rfl)] at hh
      simp only [List.replicate_succ, List.head?_cons, Option.some.injEq] at hh
      rw [← hh]
      exact le_refl _

/-- 記法系の基本列：`Ψ_π(b+1)` が標準形で `π = Ω_0` か `Ω_{c'+1}` なら、`Ψ_π(b)·(n+1)`（`fsTerm`）は
    標準形で狭義増加し、`Ψ_π(b+1)` 未満で、`Ψ_π(b+1)` 未満の標準形はどれかの `Ψ_π(b)·(n+1)` 未満 -/
theorem fs_psi_succ {pi c : Tm} (h : isNF (.Psi pi c) = true)
    (hpi : pi = .Om .zero ∨ ∃ c', pi = .Om c' ∧ isSucc c' = true) (hc : isSucc c = true) :
    isNF (.Psi pi (predT c)) = true ∧
      (∀ n, isNF (fsTerm pi (predT c) n) = true) ∧
      (∀ n, MahloOCF.lt (fsTerm pi (predT c) n) (fsTerm pi (predT c) (n + 1)) = true) ∧
      (∀ n, MahloOCF.lt (fsTerm pi (predT c) n) (.Psi pi c) = true) ∧
      (∀ x, isNF x = true → MahloOCF.lt x (.Psi pi c) = true →
        ∃ n, MahloOCF.lt x (fsTerm pi (predT c) n) = true) := by
  have g := good_of_isNF.{u} _ h
  cases g with
  | psi _ _ gpi gc hreg hact hnorm =>
    obtain ⟨gb, hvc⟩ := good_predT gc hc
    have hπ : val.{u} pi = Om 0 ∨ ∃ ζ, succ ζ < Λ ∧ val.{u} pi = Om (succ ζ) := by
      rcases hpi with e | ⟨c', e, hs⟩
      · subst e; exact Or.inl rfl
      · subst e
        have gc' : Good.{u} c' := by cases gpi with | om _ hc' _ => exact hc'
        obtain ⟨gp, hv⟩ := good_predT gc' hs
        refine Or.inr ⟨val (predT c'), ?_, by show Om (val c') = _; rw [hv]⟩
        rw [← hv]; exact gc'.inv.lt_Λ
    have hact' : Psi (val.{u} pi) (val (predT c)) < val pi := by
      rcases hπ with e | ⟨ζ, hζ, e⟩
      · rw [e]; exact Psi_Om_zero_lt _
      · rw [e]; exact Psi_Om_succ_lt hζ _
    have hnorm' : C (val.{u} (predT c)) (Psi (val pi) (val (predT c))) (val (predT c)) := by
      rw [hvc] at hnorm
      exact normal_of_normal_succ hact' hnorm
    have hact'' : ∀ m d, pi = .Xi m d → val.{u} d < val (predT c) := by
      intro m d e
      rcases hpi with e' | ⟨c', e', _⟩
      · rw [e'] at e; cases e
      · rw [e'] at e; cases e
    have gψ : Good.{u} (.Psi pi (predT c)) := Good.psi _ _ gpi gb hreg hact'' hnorm'
    have gψc : Good.{u} (.Psi pi c) := Good.psi _ _ gpi gc hreg hact hnorm
    have fs := Psi_succ_fs hπ hnorm'
    have gfs := good_fsTerm gψ
    have nfs : ∀ n, isNF (fsTerm pi (predT c) n) = true := fun n => isNF_of_good _ (gfs n)
    have hψ0 : 0 < val.{u} (Tm.Psi pi (predT c)) := Psi_pos hact'
    refine ⟨isNF_of_good _ gψ, nfs, ?_, ?_, ?_⟩
    · intro n
      rw [lt_iff_val (nfs n) (nfs (n + 1)), val_fsTerm, val_fsTerm]
      exact iterAdd_lt_succ hψ0 (n + 1)
    · intro n
      rw [lt_iff_val (nfs n) h, val_fsTerm]
      show iterAdd _ (n + 1) < Psi (val pi) (val c)
      rw [hvc]
      exact fs.1 n
    · intro x hx hlt
      rw [lt_iff_val hx h] at hlt
      have hlt' : val.{u} x < Psi (val pi) (succ (val (predT c))) := by
        have := hlt; rw [show val.{u} (Tm.Psi pi c) = Psi (val pi) (val c) from rfl, hvc] at this
        exact this
      obtain ⟨n, hn⟩ := fs.2 _ hlt'
      refine ⟨n, ?_⟩
      rw [lt_iff_val hx (nfs n), val_fsTerm]
      exact hn

end

end OCF.Mahlo
