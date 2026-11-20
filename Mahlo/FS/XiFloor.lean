import Mahlo.FS.XiSucc

/-! `Ξ_m(q)` への崩壊の後者の底 `t = Ψ_{Ξ_m(q)}(q+1)`：種は目標 `ρ = Ξ_m(q)` の前線の最大元 `P0`。

* 前線：`ρ` の前線は `M_m` についての `q` の前線（`fr_rho_iff`）。
* 移し替え（`hull_trx`）：`ρ` の前線が `y = Ξ_m(A)` の下にあり、`q` の節点の引数が `A` の下にあれば、
  `C(q, ρ)` の元は `C(A, y)` に入る。`ρ` の真の部分項で `ρ` 未満のものは `y` 未満（`floor_lowx`）、
  `t` の部分項で `t` 未満のものも同様（`gp_floor`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 最大元 -/

theorem maxL_mem : ∀ {l : List Tm} {p : Tm}, maxL l = some p → p ∈ l
  | [], _, h => by simp [maxL] at h
  | x :: xs, p, h => by
    unfold maxL at h
    cases hm : maxL xs with
    | none =>
      rw [hm] at h; cases h; exact List.mem_cons_self
    | some y =>
      rw [hm] at h
      dsimp only at h
      split at h
      · cases h; exact List.mem_cons_of_mem _ (maxL_mem hm)
      · cases h; exact List.mem_cons_self

theorem maxL_le : ∀ {l : List Tm} {p : Tm}, (∀ x, x ∈ l → WNF x) → maxL l = some p → ∀ x, x ∈ l → Le x p
  | [], _, _, h => by simp [maxL] at h
  | x :: xs, p, hF, h => by
    intro z hz
    unfold maxL at h
    cases hm : maxL xs with
    | none =>
      rw [hm] at h; cases h
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons a l =>
          exfalso
          unfold maxL at hm
          cases hm' : maxL l with
          | none => rw [hm'] at hm; cases hm
          | some y => rw [hm'] at hm; dsimp only at hm; split at hm <;> cases hm
      subst hxs
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl rfl
      · cases hz
    | some y =>
      rw [hm] at h
      dsimp only at h
      have hyF := hF y (List.mem_cons_of_mem _ (maxL_mem hm))
      have hxF := hF x List.mem_cons_self
      have ih := maxL_le (fun w hw => hF w (List.mem_cons_of_mem _ hw)) hm
      split at h
      · rename_i hxy
        cases h
        rcases List.mem_cons.mp hz with e | hz
        · rw [e]; exact Or.inr (ltB_iff.mp hxy)
        · exact ih z hz
      · rename_i hxy
        cases h
        rcases List.mem_cons.mp hz with e | hz
        · rw [e]; exact Or.inl rfl
        · have h1 := ih z hz
          have h2 : Le y x := le_of_not_ltY hxF hyF (fun h' => hxy (ltB_iff.mpr h'))
          exact le_transY (hF z (List.mem_cons_of_mem _ hz)) hyF hxF h1 h2

theorem maxL_none : ∀ {l : List Tm}, maxL l = none → l = []
  | [], _ => rfl
  | x :: xs, h => by
    unfold maxL at h
    cases hm : maxL xs with
    | none => rw [hm] at h; cases h
    | some y => rw [hm] at h; dsimp only at h; split at h <;> cases h

/-! ### 前線 -/

/-- より小さい基準の前線の元は、大きい基準の前線の元が全て小さい基準未満なら、大きい基準の前線の元 -/
theorem fr_up {R' R : Tm} (hR' : WNF R') (hR : WNF R) (hle : Lt R' R) :
    ∀ {x w : Tm}, WNF x → (∀ u, u ∈ fr R x → Lt u R') → w ∈ fr R' x → w ∈ fr R x
  | .zero, _, _, _, h | .M _, _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, hu, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_up hR' hR hle ha
        (fun u hu' => hu u (by rw [fr, List.mem_append]; exact Or.inl hu')) h)
    · exact Or.inr (fr_up hR' hR hle hb
        (fun u hu' => hu u (by rw [fr, List.mem_append]; exact Or.inr hu')) h)
  | .Om a, w, hx, hu, h => by
    rw [fr] at h ⊢
    exact fr_up hR' hR hle hx.om.1 (fun u hu' => hu u (by rw [fr]; exact hu')) h
  | .Xi m a, w, hx, hu, h => by
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Xi m a) R'
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [lt_transY hx hR' hR h1 hle]
    · simp only [h1, ↓reduceIte] at h
      have h2 : ¬ Lt (.Xi m a) R := fun h' => h1 (hu _ (by rw [fr]; simp [h']))
      simp only [h2, ↓reduceIte]
      refine fr_up hR' hR hle hx.xi.2.1 (fun u hu' => hu u ?_) h
      rw [fr]; simp only [h2, ↓reduceIte]; exact hu'
  | .Psi p a, w, hx, hu, h => by
    have hP := hx.psi
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Psi p a) R'
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [lt_transY hx hR' hR h1 hle]
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have h2 : ¬ Lt (.Psi p a) R := fun h' => h1 (hu _ (by rw [fr]; simp [h']))
      simp only [h2, ↓reduceIte, List.mem_append]
      have hu2 : ∀ u, u ∈ fr R p ∨ u ∈ fr R a → Lt u R' := fun u hu' => hu u (by
        rw [fr]; simp only [h2, ↓reduceIte, List.mem_append]; exact hu')
      rcases h with h | h
      · exact Or.inl (fr_up hR' hR hle hP.piF (fun u hu' => hu2 u (Or.inl hu')) h)
      · exact Or.inr (fr_up hR' hR hle hP.aF (fun u hu' => hu2 u (Or.inr hu')) h)

/-- `ρ = Ξ_m(q)` の前線は `M_m` についての `q` の前線 -/
theorem fr_rho_iff {m : Nat} {q w : Tm} (hρ : WNF (.Xi m q)) :
    w ∈ fr (.Xi m q) (.Xi m q) ↔ w ∈ fr (.M m) q := by
  have hMF := WNF.M' hρ.xi.1
  have hqF := hρ.xi.2.1
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have e : fr (.Xi m q) (.Xi m q) = fr (.Xi m q) q := by
    rw [fr]; simp only [Lt.irrefl, ↓reduceIte]
  rw [e]
  constructor
  · intro h
    exact fr_up hρ hMF hρM hqF (fun u hu => k2xY hρ u hu) h
  · intro h
    exact fr_subY hMF hρ (Or.inr hρM) hqF h (k2xY hρ w h)

/-- 前線の元の性質 -/
theorem fr_elem {R x w : Tm} (hx : WNF x) (h : w ∈ fr R x) :
    WNF w ∧ Lt w R ∧ isPrincipal w = true ∧ w ≠ .zero ∧ w ∈ subs x := by
  have hs := fr_spec h
  refine ⟨hx.of_mem_subs hs.1, hs.2, ?_, ?_, hs.1⟩
  · rcases fr_node h with ⟨m, a, rfl⟩ | ⟨p, a, rfl⟩ <;> rfl
  · rcases fr_node h with ⟨m, a, rfl⟩ | ⟨p, a, rfl⟩ <;> intro e <;> cases e

/-! ### `C(q, ρ)` から `C(A, Ξ_m(A))` への移し替え -/

/-- `C(q, ρ)` から `C(A, y)` への移し替え（`ρ = Ξ_m(q)`、`y = Ξ_m(A)`） -/
theorem hull_trx {m : Nat} {q A E : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hsz : E.size < (Tm.Xi m q).size)
    (hlow : ∀ n, n ∈ subs E → WNF n → ¬ Lt n (.Xi m A) → ∀ f, f ∈ fr (.M m) q → Lt f n)
    (hc1 : ∀ k a, Tm.Psi k a ∈ subs E → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs E → Lt b q → Lt b A) :
    ∀ {e : Tm}, WNF e → e ∈ subs E → inC e q (.Xi m q) = true → inC e A (.Xi m A) = true
  | .zero, _, _, _ => inC_zero _ _
  | .M _, _, _, _ => inC_M _ _ _
  | .plus a b, he, hE, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨hull_trx hρ hy hsz hlow hc1 hc1x ha (subs_trans hE (subs_plus_l (self_mem_subs a))) h.1,
      hull_trx hρ hy hsz hlow hc1 hc1x hb (subs_trans hE (subs_plus_r (self_mem_subs b))) h.2⟩
  | .Om a, he, hE, h => by
    rw [inC_om] at h ⊢
    exact hull_trx hρ hy hsz hlow hc1 hc1x he.om.1 (subs_trans hE (mem_subs_om a)) h
  | .Xi m' b, he, hE, h => by
    have hbF := he.xi.2.1
    have hS := hull_trx hρ hy hsz hlow hc1 hc1x hbF (subs_trans hE (mem_subs_xi m' b))
    have hqF := hρ.xi.2.1
    by_cases h1 : Lt (.Xi m' b) (.Xi m q)
    · by_cases hny : Lt (.Xi m' b) (.Xi m A)
      · exact inC_xi_iff.mpr (Or.inl hny)
      by_cases hl : m' = m
      · subst hl
        have hne : b ≠ q := fun e => by rw [e] at h1; exact Lt.irrefl _ h1
        rcases (lt_xi_xi0 hne).mp h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have h5 := hc1x m' b hE h3
          exact inC_xi_iff.mpr (Or.inl ((lt_xi_xi0 (Lt.ne h5)).mpr (Or.inl ⟨h5, hS h4⟩)))
        · exfalso
          have hMF := WNF.M' hρ.xi.1
          have hxM : Lt (.Xi m' b) (.M m') := xi_lt_M b
          have h5 := (inC_fr (R := .M m') (g0 := q) (g := b) (d := .Xi m' b) q hρ.xi.2.2.2
            (fun w hw hwM hwd => hwM (lt_transY (hqF.of_mem_subs hw) he hMF hwd hxM))
            (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hbF hvq h3)).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hlow _ hE he hny w hw))
          rw [h5] at h4; cases h4
      · have h0 : lev (.Xi m' b) ≤ lev (.Xi m q) := lev_le_of_lt_gen h1
        have h0' : m' < m := by simp only [lev] at h0; omega
        exact inC_xi_iff.mpr (Or.inl (lt_of_lev_lt' (by simp only [lev]; exact h0')))
    · rcases inC_xi_iff.mp h with h2 | ⟨h2, h3⟩
      · exact absurd h2 h1
      · exact inC_xi_iff.mpr (Or.inr ⟨hS h2, hc1x m' b hE h3⟩)
  | .Psi k a, he, hE, h => by
    have hP := he.psi
    have hqF := hρ.xi.2.1
    have hm := hρ.xi.1
    have hMF := WNF.M' hm
    have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
    have hS_k := hull_trx hρ hy hsz hlow hc1 hc1x hP.piF (subs_trans hE (subs_psi_p (self_mem_subs k)))
    have hS_a := hull_trx hρ hy hsz hlow hc1 hc1x hP.aF (subs_trans hE (subs_psi_a (self_mem_subs a)))
    by_cases h1 : Lt (.Psi k a) (.Xi m q)
    · by_cases hny : Lt (.Psi k a) (.Xi m A)
      · exact inC_psi_iff.mpr (Or.inl hny)
      have h0 : lev (.Psi k a) ≤ lev (.Xi m q) := lev_le_of_lt_gen h1
      by_cases hl : lev k = m
      · by_cases hρk : Lt (.Xi m q) k
        · exfalso
          have hnb := not_base_of_lt_tgtY he hρ (Or.inr (Or.inr ⟨m, q, rfl⟩)) hl hρk h1
          have hk : Lt (kTerm (m - 1)) (.Psi k a) :=
            lt_of_lt_of_leY (wnf_kTerm _) hy he (floorLev_lt_xi hy) (le_of_not_ltY he hy hny)
          have hqC : inC q q (.Psi k a) = true :=
            (inC_fr (R := .M m) (g0 := q) (g := q) (d := .Psi k a) q hρ.xi.2.2.2
              (fun w hw hwM hwd => hwM (lt_transY (hqF.of_mem_subs hw) he hMF hwd
                (lt_transY he hρ hMF h1 hρM)))
              (fun v _ hvq => hvq)).mpr
              (fun w hw => inC_of_lt_node (fr_node hw) (hlow _ hE he hny w hw))
          rw [(baseOf_xi_iff m q _).mpr ⟨hk, hqC⟩] at hnb
          cases hnb
        · have hkρ : Le k (.Xi m q) := le_of_not_ltY hρ hP.piF hρk
          have hkne : k ≠ .Xi m q := ne_of_size_lt (by
            have h3 := size_le_of_mem_subs hE
            simp only [Tm.size] at h3 hsz ⊢
            omega)
          have hkρ' : Lt k (.Xi m q) := hkρ.resolve_left hkne
          have hky := coll_xi0 hy k hP.piF (hS_k (inC_of_ltY _ hP.piF hρ hkρ'))
            (lt_transY hP.piF hρ hMF hkρ' hρM)
          exact inC_psi_iff.mpr (Or.inl (lt_transY he hP.piF hy (lt_psi_targetY he) hky))
      · have h0' : lev k < m := by simp only [lev] at h0; omega
        exact inC_psi_iff.mpr (Or.inl (lt_of_lev_lt' (by simp only [lev]; exact h0')))
    · rcases inC_psi_iff.mp h with h2 | ⟨h2, h3, h4⟩
      · exact absurd h2 h1
      · exact inC_psi_iff.mpr (Or.inr ⟨hS_k h2, hS_a h3, hc1 k a hE h4⟩)

/-- `C(q, ρ)` の元で `M_m` 未満のものは `y = Ξ_m(A)` 未満 -/
theorem hull_ltx {m : Nat} {q A v : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hsz : v.size < (Tm.Xi m q).size)
    (hlow : ∀ n, n ∈ subs v → WNF n → ¬ Lt n (.Xi m A) → ∀ f, f ∈ fr (.M m) q → Lt f n)
    (hc1 : ∀ k a, Tm.Psi k a ∈ subs v → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs v → Lt b q → Lt b A)
    (hv : WNF v) (hvM : Lt v (.M m)) (hC : inC v q (.Xi m q) = true) : Lt v (.Xi m A) :=
  coll_xi0 hy v hv (hull_trx hρ hy hsz hlow hc1 hc1x hv (self_mem_subs v) hC) hvM

/-- 前線の元が全て `y = Ξ_m(A)` 未満で、引数の条件があれば、`ρ = Ξ_m(q)` の真の部分項で `ρ` 未満のものは
`y` 未満 -/
theorem floor_lowx {m : Nat} {q A : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hF : ∀ f, f ∈ fr (.M m) q → Lt f (.Xi m A))
    (hc1 : ∀ k a, Tm.Psi k a ∈ subs q → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b A) :
    ∀ v, v ∈ subs q → Lt v (.Xi m q) → Lt v (.Xi m A) := by
  intro v hv hl
  have hqF := hρ.xi.2.1
  have hMF := WNF.M' hρ.xi.1
  have hvF := hqF.of_mem_subs hv
  have hsz : v.size < (Tm.Xi m q).size := by
    have := size_le_of_mem_subs hv; simp only [Tm.size]; omega
  exact hull_ltx hρ hy hsz
    (fun n _ hnF hn f hf => lt_of_lt_of_leY ((hqF.of_mem_subs (fr_spec hf).1)) hy hnF (hF f hf)
      (le_of_not_ltY hnF hy hn))
    (fun k a hz hlt => hc1 k a (subs_trans hv hz) hlt)
    (fun m' b hz hlt => hc1x m' b (subs_trans hv hz) hlt) hvF
    (lt_transY hvF hρ hMF hl (xi_lt_M q)) (inC_of_ltY q hvF hρ hl)

/-! ### `t = Ψ_ρ(q+1)` の部分項 -/

/-- `y` が主要項で `1`・`Ω_0`・`0` より大きいとき、`1` の部分項は `y` 未満 -/
theorem lt_of_sub_one {y v : Tm} (h1 : Lt one y) (hO : Lt (.Om .zero) y) (hy0 : Lt .zero y)
    (hv : v ∈ subs one) : Lt v y := by
  rcases mem_subs_one hv with rfl | rfl | rfl
  · exact h1
  · exact hO
  · exact hy0

theorem lt_of_sub_plus_one {t y z : Tm} (htF : WNF t) (hyp : isPrincipal y = true) (h1 : Lt one y)
    (hO : Lt (.Om .zero) y) (hy0 : Lt .zero y)
    (hsub : ∀ v, v ∈ subs z → WNF v → Lt v t → Lt v y) :
    ∀ v, v ∈ subs (Tm.plus z one) → WNF v → Lt v t → Lt v y := by
  intro v hv hvF hvt
  have hv' : v = .plus z one ∨ v ∈ subs z ∨ v ∈ subs one := by
    have : v ∈ (Tm.plus z one) :: (subs z ++ subs one) := hv
    simpa only [List.mem_cons, List.mem_append] using this
  rcases hv' with rfl | hv' | hv'
  · obtain ⟨hzF, -, -, -⟩ := hvF.plus
    exact (lt_plus_prin_iffY hvF hyp).mpr (hsub z (self_mem_subs z) hzF
      (lt_transY hzF hvF htF (lt_plus_leftY hvF) hvt))
  · exact hsub v hv' hvF hvt
  · exact lt_of_sub_one h1 hO hy0 hv'

/-- `q + 1` の部分項で `t` 未満のものは、`q` の部分項がそうなら `y` 未満（`y` は主要項） -/
theorem lt_of_sub_succT {t y : Tm} (htF : WNF t) (hyp : isPrincipal y = true) (h1 : Lt one y)
    (hO : Lt (.Om .zero) y) (hy0 : Lt .zero y) :
    ∀ z, WNF (succT z) → (∀ v, v ∈ subs z → WNF v → Lt v t → Lt v y) →
      ∀ v, v ∈ subs (succT z) → WNF v → Lt v t → Lt v y := by
  intro z
  induction z with
  | zero =>
    intro _ _ v hv _ _
    exact lt_of_sub_one h1 hO hy0 hv
  | plus a b _ ihb =>
    intro hz hsub v hv hvF hvt
    have hz' : WNF (.plus a (succT b)) := hz
    obtain ⟨ha, hb, -, -⟩ := hz'.plus
    have hv' : v ∈ subs (.plus a (succT b)) := hv
    simp only [subs, List.mem_cons, List.mem_append] at hv'
    rcases hv' with rfl | hv' | hv'
    · exact (lt_plus_prin_iffY hvF hyp).mpr (hsub a (subs_plus_l (self_mem_subs a)) ha
        (lt_transY ha hvF htF (lt_plus_leftY hvF) hvt))
    · exact hsub v (subs_plus_l hv') hvF hvt
    · exact ihb hb (fun w hw => hsub w (subs_plus_r hw)) v hv' hvF hvt
  | M n =>
    intro _ hsub v hv hvF hvt
    exact lt_of_sub_plus_one htF hyp h1 hO hy0 hsub v hv hvF hvt
  | Om n _ =>
    intro _ hsub v hv hvF hvt
    exact lt_of_sub_plus_one htF hyp h1 hO hy0 hsub v hv hvF hvt
  | Xi k n _ =>
    intro _ hsub v hv hvF hvt
    exact lt_of_sub_plus_one htF hyp h1 hO hy0 hsub v hv hvF hvt
  | Psi k n _ _ =>
    intro _ hsub v hv hvF hvt
    exact lt_of_sub_plus_one htF hyp h1 hO hy0 hsub v hv hvF hvt

/-- `t = Ψ_ρ(q + 1)` の部分項で `t` 未満のものは、`ρ` の部分項で `ρ` 未満のものが `y` 未満なら `y` 未満 -/
theorem gp_floor {ρ q y : Tm} (ht : WNF (.Psi ρ (succT q))) (hqρ : q ∈ subs ρ)
    (hyp : isPrincipal y = true) (h1 : Lt one y) (hO : Lt (.Om .zero) y) (hy0 : Lt .zero y)
    (h : ∀ v, v ∈ subs ρ → WNF v → Lt v ρ → Lt v y) :
    ∀ v, v ∈ subs (Tm.Psi ρ (succT q)) → v ≠ .Psi ρ (succT q) → Lt v (.Psi ρ (succT q)) →
      Lt v y := by
  intro v hv hne hvt
  have hρ := ht.psi.piF
  have hX := ht.psi.aF
  have hvF := ht.of_mem_subs hv
  have hρy : ∀ w, w ∈ subs ρ → WNF w → Lt w (.Psi ρ (succT q)) → Lt w y := fun w hw hwF hl =>
    h w hw hwF (lt_transY hwF ht hρ hl (lt_psi_targetY ht))
  simp only [subs, List.mem_cons, List.mem_append] at hv
  rcases hv with e | hv | hv
  · exact absurd e hne
  · exact hρy v hv hvF hvt
  · exact lt_of_sub_succT ht hyp h1 hO hy0 q hX
      (fun w hw hwF hl => hρy w (subs_trans hqρ hw) hwF hl) v hv hvF hvt

/-! ### 極限 `q` の最初の近似 -/

/-- 節点は、それより大きい基準について自身の前線 -/
theorem mem_fr_self {R p : Tm} (hn : (∃ m a, p = .Xi m a) ∨ (∃ k a, p = .Psi k a)) (h : Lt p R) :
    p ∈ fr R p := by
  rcases hn with ⟨m, a, rfl⟩ | ⟨k, a, rfl⟩ <;> simp [fr, h]

/-- 極限 `q`（最後の加数 `R`、`q ≠ M_m⁺`）の最初の近似 `s0` の 0 番目は `Ξ_m(pre ⊕ R[0])` -/
theorem s0_first_xi {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hq0 : q ≠ .zero)
    (hs : ¬ isSucc q = true) (hqS : q ≠ succM m) (hRinv : ∀ R, R ∈ summands q → Inv R) :
    ∃ R x0, summands q = (summands q).dropLast ++ [R] ∧
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums)
        .zero .zero).first = .Xi m (xa (summands q).dropLast .zero x0) ∧
      WNF x0 ∧ Lt x0 R ∧ (∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x0) ∧
      (x0 = .zero → ∀ v, v ∈ subs R → v = R) ∧ (∀ n b, R = .Xi n b → x0 = base R) ∧
      WNF (.Xi m (xa (summands q).dropLast .zero x0)) ∧ x0 = fund R .zero := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hne := summands_ne_nil hq0
  obtain ⟨R, hRdef⟩ : ∃ R, (summands q).getLast hne = R := ⟨_, rfl⟩
  have hpre : preT (info q).sums = (summands q).dropLast := preT_info q
  have hlast : lastT (info q).sums = R := by
    rw [lastT_info, List.getLast?_eq_some_getLast hne, hRdef]; rfl
  have hlastS : lastS (info q).sums = (info R).seq := by rw [lastS_coh (coh_sums q), hlast]
  have hsq : summands q = (summands q).dropLast ++ [R] := by
    rw [← hRdef]; exact (List.dropLast_concat_getLast hne).symm
  have hRq : R ∈ summands q := by rw [← hRdef]; exact List.getLast_mem hne
  have hRW := summands_WNF q hqF R hRq
  have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsq hRW.2]; exact hs
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hRi := hRinv R hRq
  rw [hpre, hlast, hlastS]
  refine ⟨R, ?_⟩
  cases hdR : dom R with
  | zero => exact absurd ((dom_eq_zero_iff hRW.1).mp hdR) hR0
  | one => exact absurd ((dom_eq_one_iff hRW.1).mp hdR) hRns
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    have hxF := hRN.props.nf 0
    refine ⟨fundNat R 0, hsq, ?_, hxF, hRN.props.lt 0, hRN.gap 0, fun h0 => absurd h0 (hRN.pos 0),
      (fun n b e => by rw [e, dom_xi] at hdR; cases hdR), ?_⟩
    · unfold SeqD.first; rw [app_xi_dom_nat hr]; exact app_xi_nat hr WNF.zero hxF
    · have hRC := G0.pre_inC hxF (hRN.gap 0) (fun h0 => absurd h0 (hRN.pos 0)) G0.hqC R (by simp)
      exact ⟨G0.nf hxF (hRN.props.lt 0) (hRN.gap 0) (fun h0 => absurd h0 (hRN.pos 0))
        (hRN.ub _ _ 0 (G0.hAF hxF) (G0.xa0 hxF (hRN.pos 0)) (Cut.of_wnf hMF) hRC),
        (fund_zero_omega hdR).symm⟩
  | big σ =>
    have hr : (info R).seq.dom = .big σ := hdR
    have hB := hRi.2 σ hdR
    have hσF := hB.props.σF
    have hσ0 := hB.props.pos
    have hxF := hB.props.nf .zero WNF.zero hσ0
    have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R .zero) :=
      fun v hv hne hlt => hB.gapP hRW.2 .zero v WNF.zero hσ0 hv hne hlt
    by_cases hσρ : Lt σ (.Xi m q)
    · refine ⟨fundBig R .zero, hsq, ?_, hxF, hB.props.lt .zero WNF.zero hσ0, hgap,
        hB.pos .zero WNF.zero hσ0, fun n b e => by rw [e, fundBig_xi, oadd_zero],
        G0.big_wnf hB (lt_transY hσF hρ hMF hσρ hρM) WNF.zero hσ0, (fund_zero_big hdR).symm⟩
      unfold SeqD.first; rw [app_xi_big_dom hr hσρ]; exact app_xi_big WNF.zero hxF
    · rcases cof_split hρ hRq hB hσρ with e | ⟨-, -, eq⟩
      · subst e
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        have hxC : inC (fundBig R .zero) (xa (summands q).dropLast .zero (fundBig R .zero)) (.M m)
            = true := by
          by_cases h0 : fundBig R .zero = .zero
          · rw [h0]; exact inC_zero _ _
          · have hRC := G0.pre_inC hxF hgap (hB.pos .zero WNF.zero hσ0) G0.hqC R (by simp)
            exact hB.ub _ _ .zero (G0.hAF hxF) (G0.xa0 hxF h0) (Cut.of_wnf hMF) WNF.zero hσ0
              (inC_kTerm _ _ _) hRC (inC_zero _ _)
        refine ⟨fundBig R .zero, hsq, ?_, hxF, hB.props.lt .zero WNF.zero hσ0, hgap,
          hB.pos .zero WNF.zero hσ0, fun n b e => by rw [e, fundBig_xi, oadd_zero],
          G0.nf hxF (hB.props.lt .zero WNF.zero hσ0) hgap (hB.pos .zero WNF.zero hσ0) hxC,
          (fund_zero_big hdR).symm⟩
        unfold SeqD.first
        rw [app_xi_M_dom hr hτ, app_xi_M_nat hr hτ, gam_xi_M_succ, gam_xi_M_zero]
        exact congrArg (Tm.Xi m) (combine_xi m _ WNF.zero hxF)
      · exact absurd eq hqS

/-- 底：`Ξ_m(pre ⊕ x0) < p`（`p` は前線の元）なら、`p` は最後の加数 `R` の前線にあり、`pre` の加数は
`p` より大きい -/
theorem floor_tail {m : Nat} {q p R x0 : Tm} (hρ : WNF (.Xi m q))
    (hsq : summands q = (summands q).dropLast ++ [R]) (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (hx0 : WNF x0) (hx0R : Lt x0 R) (hyF : WNF (.Xi m (xa (summands q).dropLast .zero x0)))
    (hlt : Lt (.Xi m (xa (summands q).dropLast .zero x0)) p) :
    p ∈ fr (.M m) R ∧ Le p R ∧ ∀ u, u ∈ (summands q).dropLast → Lt p u := by
  have hqF := hρ.xi.2.1
  have hMF := WNF.M' hρ.xi.1
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRW := summands_WNF q hqF R hRq
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  obtain ⟨hpF, hpρ, -, -, -⟩ := fr_elem hρ hpm
  have hpM : Lt p (.M m) := lt_transY hpF hρ hMF hpρ (xi_lt_M q)
  have hpq : p ∈ fr (.M m) q := (fr_rho_iff hρ).mp hpm
  have hpA : ∀ u, u ∈ (summands q).dropLast → p ∈ fr (.M m) u → False := fun u hu hpu =>
    Lt.asymmY hyF hpF hlt (k2xY hyF p (mem_fr_iff.mpr ⟨u, G0.mem_xa_pre hx0 hx0R hu, hpu⟩))
  obtain ⟨u, hu, hpu⟩ := mem_fr_iff.mp hpq
  rw [hsq] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact (hpA u hu hpu).elim
  rw [List.mem_singleton] at hu
  rw [hu] at hpu
  refine ⟨hpu, fr_leY hMF hRW.1 hpu, fun u hu' => ?_⟩
  have huq : u ∈ summands q := by rw [hsq]; exact List.mem_append_left _ hu'
  have huF := (summands_WNF q hqF u huq).1
  have hRu : Le R u := le_of_ne_gtY hRW.1 huF (nfl_append_ge G0.hNT u hu' R (by simp))
  rcases triY hpF huF with h | e | h
  · exact h
  · exfalso
    rw [← e] at hu'
    exact hpA p hu' (mem_fr_self (fr_node hpq) hpM)
  · exact absurd (lt_of_lt_of_leY huF hpF hRW.1 h (fr_leY hMF hRW.1 hpu))
      (not_lt_of_leY hRW.1 huF hRu)

/-! ### 底の種 -/

/-- 底の種 `p`（前線の元で `q` の最後の加数、`q = pre ⊕ p`）：`Ξ_m(pre ⊕ p[0]) < p` なら、
`pre ≤ c < q` の `Ξ_m(c)` は `p` 未満 -/
theorem floor_seed_lt {m : Nat} {q p x0 c : Tm} {pre : List Tm} (hρ : WNF (.Xi m q))
    (hsq : summands q = pre ++ [p]) (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (hx0 : WNF x0) (hx0p : Lt x0 p) (hgap : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v x0)
    (hbase : ∀ n b, p = .Xi n b → x0 = base p)
    (hyF : WNF (.Xi m (xa pre .zero x0))) (hlt : Lt (.Xi m (xa pre .zero x0)) p)
    (hc : WNF (.Xi m c)) (hcρ : Lt (.Xi m c) (.Xi m q)) (hcq : Lt c q)
    (hcT : ¬ Lt c (ofSummands pre)) : Lt (.Xi m c) p := by
  have hqF := hρ.xi.2.1
  have hm := hρ.xi.1
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  obtain ⟨hpF, hpρ, -, hp0, -⟩ := fr_elem hρ hpm
  have hpM := lt_transY hpF hρ hMF hpρ hρM
  have hpq : p ∈ summands q := by rw [hsq]; simp
  have G0 : XG m q .zero pre [] p :=
    ⟨hρ, hsq, WNF.zero, zero_lt hp0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hAF := G0.hAF hx0
  have hpreF := G0.hpreF
  have hcF := hc.xi.2.1
  have hx0y : Lt x0 (.Xi m (xa pre .zero x0)) :=
    coll_xi0 hyF x0 hx0 (G0.parts hx0 hx0p (xi_selfY hyF)).2.2 (lt_transY hx0 hpF hMF hx0p hpM)
  have hgy : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v (.Xi m (xa pre .zero x0)) :=
    fun v hv hne hl => lt_transY (hpF.of_mem_subs hv) hx0 hyF (hgap v hv hne hl) hx0y
  have hk : Lt (kTerm (m - 1)) p := lt_transY (wnf_kTerm _) hyF hpF (floorLev_lt_xi hyF) hlt
  have hlp : lev p = m := by
    have h1 : lev p ≤ m := by have := lev_le_of_lt_gen hpρ; simpa [lev] using this
    rcases Nat.lt_or_ge (lev p) m with h2 | h2
    · exact absurd hlt (Lt.asymmY hpF hyF (lt_of_lev_lt' (by simp only [lev]; exact h2)))
    · omega
  -- `c` の加数は `pre` の元か `p` 未満
  have hcsum : ∀ u, u ∈ summands c → u ∈ pre ∨ Lt u p := by
    rcases lt_split hqF hsq hcF hcq with hle | ⟨c', hc', -, hc'p, hsc, -⟩
    · have e : c = ofSummands pre := by
        rcases hle with e | h
        · exact e
        · exact absurd h hcT
      intro u hu
      rw [e, summands_ofSummands _ (nfl_principal (nfl_append_left G0.hNT))] at hu
      exact Or.inl hu
    · intro u hu
      rw [hsc] at hu
      rcases List.mem_append.mp hu with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_ltY (summands_WNF c' hc' u h).1 hc' hpF (le_of_mem_summands hc' h)
          hc'p)
  have hAsum : ∀ u, u ∈ pre → u ∈ summands (xa pre .zero x0) := fun u hu => G0.mem_xa_pre hx0 hx0p hu
  -- `A < pre ⊕ d'` なら `x0 < d'`
  have hcancel : ∀ d d', summands d = pre ++ summands d' → Lt (xa pre .zero x0) d → Lt x0 d' := by
    intro d d' hsd h
    have h1 : cmp (xa pre .zero x0) d = .lt := h
    rw [cmp_eq, G0.summands_xa hx0 hx0p, hsd, cmpList_append_same, zero_nsum _ hx0] at h1
    unfold Lt; rw [cmp_eq]; exact h1
  rcases fr_node hpm with ⟨n, b, hpe⟩ | ⟨κ, β, hpe⟩
  · -- `p = Ξ_m(b)`
    have hn : n = m := by rw [hpe] at hlp; exact hlp
    rw [hn] at hpe
    subst hpe
    have hbF := hpF.xi.2.1
    have hx0e : x0 = .Psi (.Xi m b) (succT b) := hbase m b rfl
    have hx0' : WNF (.Psi (.Xi m b) (succT b)) := by rw [← hx0e]; exact hx0
    have hx0b : baseOf (.Xi m b) x0 = true := by rw [hx0e]; exact base_selfY hx0'
    obtain ⟨-, hbC⟩ := (baseOf_xi_iff m b x0).mp hx0b
    have hAb : xa pre .zero x0 ≠ b := fun e => by rw [e] at hlt; exact Lt.irrefl _ hlt
    rcases (lt_xi_xi0 hAb).mp hlt with ⟨hAb', hAC⟩ | ⟨hbA, hbnC⟩
    · have hqb : Lt q b := by
        rcases triY hqF hbF with h | e | h
        · exact h
        · exfalso; rw [e] at hpρ; exact Lt.irrefl _ hpρ
        · exfalso
          rcases lt_split hqF hsq hbF h with hle | ⟨b', hb', -, hb'p, hsb, -⟩
          · exact not_lt_of_leY hbF hAF
              (le_transY hbF hpreF hAF hle (le_oadd_leftW hpreF (G0.hyF hx0))) hAb'
          · have hx0b' := hcancel b b' hsb hAb'
            have hb'C : inC b' b x0 = true := (inC_iff_summandsW hb').mpr (fun u hu =>
              inC_of_mem_summands hbF hbC (by rw [hsb]; exact List.mem_append_right _ hu))
            have hb'C' : inC b' (succT b) x0 = true := inC_mono b' b x0 (succT b) x0 hb'C
              (fun _ _ h => h)
              (fun v hv hvb => lt_transY (hb'.of_mem_subs hv) hbF (succT_WNF hbF) hvb (lt_succT b))
            rw [hx0e] at hb'C' hx0b'
            exact Lt.asymmY hx0' hb' hx0b' (coll_psiY hx0' hb' hb'C' hb'p)
      have hcb : Lt c b := lt_transY hcF hqF hbF hcq hqb
      refine (lt_xi_xi0 (Lt.ne hcb)).mpr (Or.inl ⟨hcb, (inC_iff_summandsW hcF).mpr (fun u hu => ?_)⟩)
      rcases hcsum u hu with h | h
      · exact inC_of_mem_summands hAF hAC (hAsum u h)
      · exact inC_of_ltY _ (summands_WNF c hcF u hu).1 hpF h
    · exfalso
      have := inC_mono b b x0 (xa pre .zero x0) (.Xi m (xa pre .zero x0)) hbC
        (fun v hv hvx => lt_transY (hbF.of_mem_subs hv) hx0 hyF hvx hx0y)
        (fun v hv hvb => lt_transY (hbF.of_mem_subs hv) hbF hAF hvb hbA)
      rw [this] at hbnC; cases hbnC
  · -- `p = Ψ_κ(β)`
    subst hpe
    have hP := hpF.psi
    have hκF := hP.piF
    have hlκ : lev κ = m := hlp
    have hκp : Lt (.Psi κ β) κ := lt_psi_targetY hpF
    have hρκ : Lt (.Xi m q) κ := by
      rcases triY hκF hρ with hκρ | e | h
      · exfalso
        have hyκ : Lt (.Xi m (xa pre .zero x0)) κ := lt_transY hyF hpF hκF hlt hκp
        have hOF : IsOF (Tm.Xi m (xa pre .zero x0)) := Or.inl ⟨_, _, rfl⟩
        rcases hP.tgt with e | ⟨c₀, e, hcs⟩ | ⟨n', d, e⟩
        · subst e
          exact Lt.asymmY hyF hκF hyκ ((lt_om_OFG hOF hyF).mpr (zero_lt (by intro e; cases e)))
        · subst e
          have hc₀p : Lt c₀ (.Psi (.Om c₀) β) := cxY hpF hcs
          have hc₀s : c₀ ∈ subs (Tm.Psi (.Om c₀) β) := subs_psi_p (mem_subs_om c₀)
          exact Lt.asymmY hyF hκF hyκ ((lt_om_OFG hOF hyF).mpr (hgy c₀ hc₀s (Lt.ne hc₀p) hc₀p))
        · have hn' : n' = m := by rw [e] at hlκ; exact hlκ
          rw [hn'] at e
          subst e
          have hdF := hκF.xi.2.1
          have hAd : xa pre .zero x0 ≠ d := fun e => by rw [e] at hyκ; exact Lt.irrefl _ hyκ
          obtain ⟨-, hdC⟩ := (baseOf_xi_iff m d _).mp (base_selfY hpF)
          rcases (lt_xi_xi0 hAd).mp hyκ with ⟨hAd', hAC⟩ | ⟨hdA, hdnC⟩
          · rcases triY hdF hqF with h | e | h
            · rcases lt_split hqF hsq hdF h with hle | ⟨d', hd', hd'0, hd'p, hsd, -⟩
              · exact not_lt_of_leY hdF hAF
                  (le_transY hdF hpreF hAF hle (le_oadd_leftW hpreF (G0.hyF hx0))) hAd'
              · have hx0d' := hcancel d d' hsd hAd'
                have hd's : d' ∈ subs (Tm.Psi (.Xi m d) β) :=
                  subs_psi_p (subs_xi (tail_mem_subs pre hdF hd' hd'0 hsd))
                exact Lt.asymmY hx0 hd' hx0d' (hgap d' hd's (Lt.ne hd'p) hd'p)
            · rw [e] at hκρ; exact Lt.irrefl _ hκρ
            · have hdq : d ≠ q := fun e => by rw [e] at h; exact Lt.irrefl _ h
              rcases (lt_xi_xi0 hdq).mp hκρ with ⟨hdq', -⟩ | ⟨-, hqnC⟩
              · exact Lt.asymmY hdF hqF hdq' h
              · have hqC : inC q d (.Xi m d) = true := (inC_iff_summandsW hqF).mpr (fun u hu => by
                  rw [hsq] at hu
                  rcases List.mem_append.mp hu with h' | h'
                  · exact inC_of_mem_summands hAF hAC (hAsum u h')
                  · rw [List.mem_singleton.mp h']; exact inC_of_ltY _ hpF hκF hκp)
                rw [hqC] at hqnC; cases hqnC
          · have hsz : ∀ v, v ∈ subs d → v ≠ Tm.Psi (.Xi m d) β := fun v hv => ne_of_size_lt (by
              have := size_le_of_mem_subs hv; simp only [Tm.size]; omega)
            have := inC_mono_node d d (.Psi (.Xi m d) β) (xa pre .zero x0) (.Xi m (xa pre .zero x0))
              hdC (fun v hv _ hvp => hgy v (subs_psi_p (subs_xi hv)) (hsz v hv) hvp)
              (fun v hv _ hvd => lt_transY (hdF.of_mem_subs hv) hdF hAF hvd hdA)
            rw [this] at hdnC; cases hdnC
      · exfalso
        have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands hpq)
        rw [e] at h1
        simp only [Tm.size] at h1
        omega
      · exact h
    refine (lt_xi_psi_iff (π := κ) (γ := β) (f := c) (n := m) hlκ).mpr ⟨?_, ?_⟩
    · have h1 : Lt (.Xi m c) κ := lt_transY hc hρ hκF hcρ hρκ
      have h2 : cmp (.Xi m c) κ = .lt := h1
      rw [swapY hc hκF, h2]; rfl
    · refine (baseOf_xi_iff m c _).mpr ⟨hk, ?_⟩
      have hAp : inC (xa pre .zero x0) (xa pre .zero x0) (.Psi κ β) = true :=
        ((baseOf_xi_iff m _ _).mp
          ((lt_xi_psi_iff (π := κ) (γ := β) (f := xa pre .zero x0) (n := m) hlκ).mp hlt).2).2
      refine (inC_iff_summandsW hcF).mpr (fun u hu => ?_)
      rcases hcsum u hu with h | h
      · have huq : u ∈ summands q := by rw [hsq]; exact List.mem_append_left _ h
        have huF := (summands_WNF q hqF u huq).1
        refine inC_mono_node u (xa pre .zero x0) _ c _ (inC_of_mem_summands hAF hAp (hAsum u h))
          (fun _ _ _ h' => h') (fun v hv hvs hvA => ?_)
        have hvF := huF.of_mem_subs hv
        have hvq : Lt v q := lt_transY hvF hAF hqF hvA (G0.hAq hx0 hx0p)
        have hne : pre ≠ [] := List.ne_nil_of_mem h
        obtain ⟨pre', ul, hpe⟩ : ∃ pre' ul, pre = pre' ++ [ul] :=
          ⟨pre.dropLast, pre.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
        have hsq' : summands q = pre' ++ ul :: [Tm.Psi κ β] := by rw [hsq, hpe]; simp
        have h1 := lt_T_of_sub hqF hsq' (by rw [← hpe]; exact h) hv (ne_of_size_lt hvs) hvF hvq
        rw [← hpe] at h1
        exact lt_of_lt_of_leY hvF hpreF hcF h1 (le_of_not_ltY hcF hpreF hcT)
      · exact inC_of_ltY _ (summands_WNF c hcF u hu).1 hpF h

/-- 底の種 `P0`（目標 `Ξ_m(q)` の前線の元）は、`s0` の 0 番目より大きければ `SeedHyp` を満たす -/
theorem seedHyp_floor {m : Nat} {q p : Tm} (hρ : WNF (.Xi m q)) (hq0 : q ≠ .zero)
    (hs : ¬ isSucc q = true) (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (h1 : ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = true)
    (h2 : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first ≠ p) : SeedHyp m q p := by
  have hqF := hρ.xi.2.1
  obtain ⟨hpF, hpρ, -, -, -⟩ := fr_elem hρ hpm
  by_cases hqS : q = succM m
  · -- `q = M_m⁺`：加数 `M_m⁺` は `p` より大きく、仮定は空
    intro L₁ L₂ hsq hL₂ c _ _ hcq hcT
    exfalso
    have hMF := WNF.M' hρ.xi.1
    have hpS : Lt p q := by
      rw [hqS]
      exact lt_transY hpF hρ (WNF.succM hρ.xi.1) hpρ
        (lt_transY hρ hMF (WNF.succM hρ.xi.1) (xi_lt_M q) (M_lt_succM hρ.xi.1))
    have e1 : summands q = [q] := by rw [hqS]; rfl
    rw [e1] at hsq
    rcases List.append_eq_singleton_iff.mp hsq.symm with ⟨-, e3⟩ | ⟨e2, -⟩
    · exact not_lt_of_leY hqF hpF (hL₂ q (by rw [e3]; simp)) hpS
    · rw [e2] at hcT
      exact hcT (by simpa [ofSummands] using hcq)
  obtain ⟨R, x0, hsq, hfirst, hx0, hx0R, hgap, -, hbase, hyF, -⟩ := s0_first_xi hρ hq0 hs hqS hRinv
  rw [hfirst] at h1 h2
  have hlt : Lt (.Xi m (xa (summands q).dropLast .zero x0)) p := by
    rcases triY hyF hpF with h | e | h
    · exact h
    · exact absurd e h2
    · exact absurd (ltB_iff.mpr h) h1
  obtain ⟨-, hpleR, hpre⟩ := floor_tail hρ hsq hpm hx0 hx0R hyF hlt
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRF := (summands_WNF q hqF R hRq).1
  intro L₁ L₂ hsq' hL₂ c hc hcρ hcq hcT
  refine Or.inr ?_
  rw [hsq] at hsq'
  -- `L₁ = pre`、`L₂ = [R]`、`R = p`
  have key : L₁ = (summands q).dropLast ∧ L₂ = [R] := by
    rcases List.append_eq_append_iff.mp hsq' with ⟨a', e1, e2⟩ | ⟨c', e1, e2⟩
    · -- `L₁ = pre ++ a'`、`[R] = a' ++ L₂`
      cases a' with
      | nil => simp at e1 e2; exact ⟨e1, e2.symm⟩
      | cons x xs =>
        exfalso
        have e3 := List.cons.inj e2
        have e4 : xs = [] ∧ L₂ = [] := List.append_eq_nil_iff.mp e3.2.symm
        rw [e4.2] at hsq'
        have hL1 : ofSummands L₁ = q := by
          have : L₁ = summands q := by rw [hsq]; simpa using hsq'.symm
          rw [this]; exact ofSummands_summands q hqF
        rw [hL1] at hcT
        exact hcT hcq
    · -- `pre = L₁ ++ c'`、`L₂ = c' ++ [R]`
      cases c' with
      | nil => simp at e1 e2; exact ⟨e1.symm, e2⟩
      | cons x xs =>
        exfalso
        have hx1 : x ∈ (summands q).dropLast := by rw [e1]; simp
        have hx2 : x ∈ L₂ := by rw [e2]; simp
        have hxF := (summands_WNF q hqF x (by rw [hsq]; exact List.mem_append_left _ hx1)).1
        exact not_lt_of_leY hxF hpF (hL₂ x hx2) (hpre x hx1)
  obtain ⟨eL1, eL2⟩ := key
  have hRp : R = p := le_antisymmY hRF hpF (hL₂ R (by rw [eL2]; simp)) hpleR
  subst hRp
  rw [eL1] at hcT
  exact floor_seed_lt hρ hsq hpm hx0 hx0R hgap hbase hyF hlt hc hcρ hcq hcT

/-- 底では `s0` の 0 番目は前線の元でない -/
theorem floor_first_ne {m : Nat} {q p : Tm} (hρ : WNF (.Xi m q)) (hq0 : q ≠ .zero)
    (hs : ¬ isSucc q = true) (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (he : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p) : False := by
  have hqF := hρ.xi.2.1
  have hpq : p ∈ fr (.M m) q := (fr_rho_iff hρ).mp hpm
  by_cases hqS : q = succM m
  · obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := preT (info q).sums)
      (R := lastT (info q).sums) (r := lastS (info q).sums) (P := .zero) (c := .zero)
    rw [hA] at he
    have hps := (fr_spec hpq).1
    rw [hqS, ← he] at hps
    simp [succM, subs, one] at hps
  obtain ⟨R, x0, hsq, hfirst, hx0, hx0R, hgap, hpos, -, hyF, -⟩ := s0_first_xi hρ hq0 hs hqS hRinv
  rw [hfirst] at he
  subst he
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRW := summands_WNF q hqF R hRq
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  obtain ⟨u, hu, hpu⟩ := mem_fr_iff.mp hpq
  rw [hsq] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact Lt.irrefl _ (k2xY hyF _ (mem_fr_iff.mpr ⟨u, G0.mem_xa_pre hx0 hx0R hu, hpu⟩))
  · rw [List.mem_singleton] at hu
    rw [hu] at hpu
    have hpR := (fr_spec hpu).1
    have hAs : xa (summands q).dropLast .zero x0 ∈ subs R := subs_trans hpR (mem_subs_xi m _)
    have hAne : xa (summands q).dropLast .zero x0 ≠ R := ne_of_size_lt (by
      have := size_le_of_mem_subs hpR; simp only [Tm.size] at this ⊢; omega)
    have h := argCond hqF hsq hx0 hgap hpos R hRq _ hAs hAne (G0.hAq hx0 hx0R)
    have e : xa (summands q).dropLast .zero x0 = oadd (ofSummands (summands q).dropLast) x0 := by
      show oadd _ (nsum .zero x0) = _; rw [zero_nsum _ hx0]
    rw [← e] at h
    exact Lt.irrefl _ h

/-! ### 底の隙間 -/

/-- 節点（`Ξ`・`Ψ`）の部分項は、ある加数の部分項 -/
theorem node_mem_summand : ∀ {x n : Tm}, ((∃ m a, n = .Xi m a) ∨ (∃ k a, n = .Psi k a)) →
    n ∈ subs x → ∃ s, s ∈ summands x ∧ n ∈ subs s
  | .zero, n, hn, h => by
    simp only [subs, List.mem_singleton] at h; subst h
    rcases hn with ⟨m, a, e⟩ | ⟨k, a, e⟩ <;> cases e
  | .plus a b, n, hn, h => by
    have h' : n = .plus a b ∨ n ∈ subs a ∨ n ∈ subs b := by
      simpa only [subs, List.mem_cons, List.mem_append] using h
    rcases h' with e | h' | h'
    · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
    · exact ⟨a, by simp [summands], h'⟩
    · obtain ⟨s, hs, hns⟩ := node_mem_summand hn h'
      exact ⟨s, by rw [summands_plus]; exact List.mem_cons_of_mem _ hs, hns⟩
  | .M k, n, _, h => ⟨_, by simp [summands], h⟩
  | .Om k, n, _, h => ⟨_, by simp [summands], h⟩
  | .Xi j k, n, _, h => ⟨_, by simp [summands], h⟩
  | .Psi j k, n, _, h => ⟨_, by simp [summands], h⟩

/-- 和の部分項：加数の部分項で `B` 未満のものが主要項 `y` 未満なら、全体の部分項で `B` 未満のものも -/
theorem lt_of_summands_sub {y B : Tm} (hBF : WNF B) (hyp : isPrincipal y = true) (hy0 : Lt .zero y) :
    ∀ {x : Tm}, WNF x → (∀ s, s ∈ summands x → ∀ w, w ∈ subs s → WNF w → Lt w B → Lt w y) →
      ∀ v, v ∈ subs x → WNF v → Lt v B → Lt v y
  | .zero, _, _, v, hv, _, _ => by
    simp only [subs, List.mem_singleton] at hv; rw [hv]; exact hy0
  | .plus a b, hx, h, v, hv, hvF, hvB => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    have hv' : v = .plus a b ∨ v ∈ subs a ∨ v ∈ subs b := by
      simpa only [subs, List.mem_cons, List.mem_append] using hv
    rcases hv' with rfl | hv' | hv'
    · exact (lt_plus_prin_iffY hvF hyp).mpr (h a (by simp [summands]) a (self_mem_subs a) ha
        (lt_transY ha hvF hBF (lt_plus_leftY hvF) hvB))
    · exact h a (by simp [summands]) v hv' hvF hvB
    · exact lt_of_summands_sub hBF hyp hy0 hb (fun s hs w hw hwF hwB =>
        h s (by rw [summands_plus]; exact List.mem_cons_of_mem _ hs) w hw hwF hwB) v hv' hvF hvB
  | .M k, _, h, v, hv, hvF, hvB => h _ (by simp [summands]) v hv hvF hvB
  | .Om k, _, h, v, hv, hvF, hvB => h _ (by simp [summands]) v hv hvF hvB
  | .Xi j k, _, h, v, hv, hvF, hvB => h _ (by simp [summands]) v hv hvF hvB
  | .Psi j k, _, h, v, hv, hvF, hvB => h _ (by simp [summands]) v hv hvF hvB

/-- `z + 1` の節点は `z` の部分項か `1` -/
theorem node_sub_succT : ∀ {z n : Tm}, ((∃ m a, n = .Xi m a) ∨ (∃ k a, n = .Psi k a)) →
    n ∈ subs (succT z) → n ∈ subs z ∨ n = one
  | .zero, n, hn, h => by
    rcases mem_subs_one h with e | e | e
    · exact Or.inr e
    · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
    · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
  | .plus a b, n, hn, h => by
    have h' : n = .plus a (succT b) ∨ n ∈ subs a ∨ n ∈ subs (succT b) := by
      have h0 : n ∈ subs (Tm.plus a (succT b)) := h
      simpa only [subs, List.mem_cons, List.mem_append] using h0
    rcases h' with e | h' | h'
    · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
    · exact Or.inl (subs_plus_l h')
    · rcases node_sub_succT hn h' with h'' | h''
      · exact Or.inl (subs_plus_r h'')
      · exact Or.inr h''
  | .M k, n, hn, h => node_sub_plus_one hn h
  | .Om k, n, hn, h => node_sub_plus_one hn h
  | .Xi j k, n, hn, h => node_sub_plus_one hn h
  | .Psi j k, n, hn, h => node_sub_plus_one hn h
where
  node_sub_plus_one {z n : Tm} (hn : (∃ m a, n = .Xi m a) ∨ (∃ k a, n = .Psi k a))
      (h : n ∈ subs (Tm.plus z one)) : n ∈ subs z ∨ n = one := by
    have h' : n = .plus z one ∨ n ∈ subs z ∨ n ∈ subs one := by
      simpa only [subs, List.mem_cons, List.mem_append] using h
    rcases h' with e | h' | h'
    · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
    · exact Or.inl h'
    · rcases mem_subs_one h' with e | e | e
      · exact Or.inr e
      · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e
      · subst e; rcases hn with ⟨m, x, e⟩ | ⟨k, x, e⟩ <;> cases e

/-- 族の閉包の 0 番目は `Ξ_m(A)` か `Ω` の塔の 1 段目 -/
theorem mahloVK_first_form (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    (∃ A, (mahloVK m q qs ceil P).first = .Xi m A) ∨
      (∃ G, (mahloVK m q qs ceil P).first = .Om (sc G)) := by
  have hApp : ∀ (pre : List Tm) (R : Tm) (r : SeqD) (P' : Tm),
      (∃ A, (match mkApp ceil (.xi m) pre R r P' .zero with
        | some sq => sq | none => SeqD.tower P').first = .Xi m A) ∨
      (∃ G, (match mkApp ceil (.xi m) pre R r P' .zero with
        | some sq => sq | none => SeqD.tower P').first = .Om (sc G)) := by
    intro pre R r P'
    unfold mkApp
    by_cases h : P' ≠ zero ∧ ltB P' R = false
    · rw [ite_eq_left h]; exact Or.inr ⟨_, rfl⟩
    · rw [ite_eq_right h]; exact Or.inl app_xi_first
  unfold mahloVK
  by_cases hq0 : q = zero
  · rw [ite_eq_left hq0]; exact Or.inr ⟨_, rfl⟩
  rw [ite_eq_right hq0]
  by_cases hs : isSucc q = true
  · rw [ite_eq_left hs]
    dsimp only
    cases splitPosD ceil qs.dropLast with
    | none => exact Or.inr ⟨_, rfl⟩
    | some val =>
      obtain ⟨pre, R, r⟩ := val
      exact hApp pre R r _
  · rw [ite_eq_right hs]
    dsimp only
    cases P with
    | none => exact Or.inl app_xi_first
    | some p =>
      dsimp only
      by_cases h1 : ltB p (SeqD.app ceil (.xi m) (preT qs) (lastT qs) (lastS qs) .zero .zero).first = true
      · rw [ite_eq_left h1]; exact Or.inl app_xi_first
      · rw [ite_eq_right h1]
        by_cases h2 : (SeqD.app ceil (.xi m) (preT qs) (lastT qs) (lastS qs) .zero .zero).first = p
        · rw [ite_eq_left h2]; exact Or.inl app_xi_first
        · rw [ite_eq_right h2]
          cases splitGtD p qs with
          | none => exact Or.inr ⟨_, rfl⟩
          | some val =>
            obtain ⟨pre, R, r⟩ := val
            exact hApp pre R r p

/-- 族の閉包の 0 番目（標準形）は `1`・`Ω_0`・`0` より大きい -/
theorem mahloVK_first_big {m : Nat} {q : Tm} {qs : DL} {ceil : Tm} {P : Option Tm}
    (hF : WNF (mahloVK m q qs ceil P).first) :
    Lt one (mahloVK m q qs ceil P).first ∧ Lt (.Om .zero) (mahloVK m q qs ceil P).first ∧
      Lt .zero (mahloVK m q qs ceil P).first ∧ isPrincipal (mahloVK m q qs ceil P).first = true := by
  rcases mahloVK_first_form m q qs ceil P with ⟨A, hA⟩ | ⟨G, hG⟩
  · rw [hA] at hF ⊢
    exact ⟨one_lt_xi hF, (lt_om_OFG (Or.inl ⟨_, _, rfl⟩) hF).mpr (zero_lt (by intro e; cases e)),
      zero_lt (by intro e; cases e), rfl⟩
  · rw [hG] at hF ⊢
    have hO : Lt (.Om .zero) (.Om (sc G)) := lt_om_iffG.mpr (zero_lt (by
      intro e; have := lt_succT G; unfold sc at e; rw [e] at this; exact not_lt_zero _ this))
    exact ⟨lt_transY WNF.one WNF.om_zero hF (lt_psi_targetY WNF.one) hO, hO,
      zero_lt (by intro e; cases e), rfl⟩

/-- 加数 `R` での近似 `app`（種 `P'`）の 0 番目は `Ξ_m(A₀)` で、`P'` より大きく、`pre ++ [R]` の加数の
真の部分項で `q` 未満のものは `A₀` 未満 -/
theorem app_first_xi {m : Nat} {q P' R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRi : Inv R) (hR1 : ¬ isSucc R = true) (hRS : R ≠ succM m) :
    ∃ A₀, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first = .Xi m A₀ ∧
      WNF (.Xi m A₀) ∧ Lt P' (.Xi m A₀) ∧
      ∀ s, s ∈ pre ++ [R] → ∀ a, a ∈ subs s → a ≠ s → Lt a q → Lt a A₀ := by
  have hρ := G.ht
  have hMF := G.hMF
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hRF := G.hRF
  have hqF := G.hqF
  have hpreF := G.hpreF
  have hPF := G.hPF
  have hR0 := G.hR0
  have hcore : ∀ x, WNF x → (∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) →
      (x = .zero → ∀ v, v ∈ subs R → v = R) →
      ∀ s, s ∈ pre ++ [R] → ∀ a, a ∈ subs s → a ≠ s → Lt a q → Lt a (oadd (ofSummands pre) x) := by
    intro x hx hgap hpos s hs a ha hne haq
    have haF := ((G.hNT.1 s hs).1).of_mem_subs ha
    have h1 := lt_T_of_sub hqF G.hsum hs ha hne haF haq
    exact argCond G.hTF G.hsT hx hgap hpos s (by rw [G.hsT]; exact hs) a ha hne h1
  have hle : ∀ x, WNF x → Le (oadd (ofSummands pre) x) (xa pre P' x) := by
    intro x hx
    rcases le_nsum_right hPF hx with e | h
    · exact Or.inl (by show oadd _ x = oadd _ (nsum P' x); rw [← e])
    · exact Or.inr (oadd_lt_oadd hpreF hx (G.hyF hx) h)
  have hfin : ∀ x, WNF x → (∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) →
      (x = .zero → ∀ v, v ∈ subs R → v = R) →
      ∀ s, s ∈ pre ++ [R] → ∀ a, a ∈ subs s → a ≠ s → Lt a q → Lt a (xa pre P' x) :=
    fun x hx hgap hpos s hs a ha hne haq =>
      lt_of_lt_of_leY (((G.hNT.1 s hs).1).of_mem_subs ha) (wnf_oadd hpreF hx) (G.hAF hx)
        (hcore x hx hgap hpos s hs a ha hne haq) (hle x hx)
  cases hdR : dom R with
  | zero => exact absurd ((dom_eq_zero_iff hRF).mp hdR) hR0
  | one => exact absurd ((dom_eq_one_iff hRF).mp hdR) hR1
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    have hxF := hRN.props.nf 0
    have hpos : fundNat R 0 = .zero → ∀ v, v ∈ subs R → v = R := fun h0 => absurd h0 (hRN.pos 0)
    have hxC : inC (fundNat R 0) (xa pre P' (fundNat R 0)) (.M m) = true := by
      have hRC := G.pre_inC hxF (hRN.gap 0) hpos G.hqC R (by simp)
      exact hRN.ub _ _ 0 (G.hAF hxF) (G.xa0 hxF (hRN.pos 0)) (Cut.of_wnf hMF) hRC
    have hyF := G.nf hxF (hRN.props.lt 0) (hRN.gap 0) hpos hxC
    refine ⟨xa pre P' (fundNat R 0), ?_, hyF, G.seed_lt hxF (hRN.props.lt 0) hyF,
      hfin _ hxF (hRN.gap 0) hpos⟩
    unfold SeqD.first; rw [app_xi_dom_nat hr]; exact app_xi_nat hr hPF hxF
  | big σ =>
    have hr : (info R).seq.dom = .big σ := hdR
    have hB := hRi.2 σ hdR
    have hσF := hB.props.σF
    have hσ0 := hB.props.pos
    have hRp := G.hRp
    by_cases hσρ : Lt σ (.Xi m q)
    · have hxF := hB.props.nf .zero WNF.zero hσ0
      have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R .zero) :=
        fun v hv hne hlt => hB.gapP hRp .zero v WNF.zero hσ0 hv hne hlt
      have hyF := G.big_wnf hB (lt_transY hσF hρ hMF hσρ hρM) WNF.zero hσ0
      refine ⟨xa pre P' (fundBig R .zero), ?_, hyF,
        G.seed_lt hxF (hB.props.lt .zero WNF.zero hσ0) hyF,
        hfin _ hxF hgap (hB.pos .zero WNF.zero hσ0)⟩
      unfold SeqD.first; rw [app_xi_big_dom hr hσρ]; exact app_xi_big hPF hxF
    · rcases cof_split hρ G.hRq hB hσρ with e | ⟨-, eR, -⟩
      · subst e
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        have hPM := G.hPM
        have hxF := hB.props.nf P' hPF hPM
        have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R P') :=
          fun v hv hne hlt => hB.gapP hRp P' v hPF hPM hv hne hlt
        have G0 : XG m q .zero pre rest R :=
          ⟨hρ, G.hsum, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
        have hpos := hB.pos P' hPF hPM
        have hxC : inC (fundBig R P') (xa pre .zero (fundBig R P')) (.M m) = true := by
          by_cases h0 : fundBig R P' = .zero
          · rw [h0]; exact inC_zero _ _
          · have hRC := G0.pre_inC hxF hgap hpos G0.hqC R (by simp)
            exact hB.ub _ _ P' (G0.hAF hxF) (G0.xa0 hxF h0) (Cut.of_wnf hMF) hPF hPM
              (inC_kTerm _ _ _) hRC (inC_of_ltY _ hPF hMF hPM)
        have hyF := G0.nf hxF (hB.props.lt P' hPF hPM) hgap hpos hxC
        have hPy : Lt P' (.Xi m (xa pre .zero (fundBig R P'))) := by
          have h1 := (G0.parts hxF (hB.props.lt P' hPF hPM) (xi_selfY hyF)).2.2
          have h2 := hB.lo _ _ P' (Cut.of_wnf hyF) hPF hPM h1
          exact coll_xi0 hyF P' hPF h2 hPM
        have e : xa pre .zero (fundBig R P') = oadd (ofSummands pre) (fundBig R P') := by
          show oadd _ (nsum .zero _) = _; rw [zero_nsum _ hxF]
        refine ⟨xa pre .zero (fundBig R P'), ?_, hyF, hPy,
          fun s hs a ha hne haq => by rw [e]; exact hcore _ hxF hgap hpos s hs a ha hne haq⟩
        unfold SeqD.first
        rw [app_xi_M_dom hr hτ, app_xi_M_nat hr hτ, gam_xi_M_succ, gam_xi_M_zero]
        exact congrArg (Tm.Xi m) (combine_xi m _ WNF.zero hxF)
      · exact absurd eR hRS

/-- `M_m⁺` は後者でない -/
theorem not_isSucc_succM (m : Nat) : ¬ isSucc (succM m) = true := by
  simp [succM, isSucc, summands, one]

/-- 底の隙間：`q` の部分項で `Ξ_m(q)` 未満のものは、族の閉包の列の 0 番目未満 -/
theorem floor_gap {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hfF : WNF (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first) :
    ∀ v, v ∈ subs q → WNF v → Lt v (.Xi m q) →
      Lt v (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hSF := WNF.succM hm
  obtain ⟨h1f, hOf, h0f, -⟩ := mahloVK_first_big hfF
  obtain ⟨P0, hP0⟩ : ∃ P0, maxL (frB (.Xi m q) (.Xi m q)) = P0 := ⟨_, rfl⟩
  rw [hP0] at hfF h1f hOf h0f ⊢
  have hPe : ∀ p, P0 = some p → p ∈ fr (.Xi m q) (.Xi m q) := fun p hp => by
    rw [← frB_eq_fr]; rw [hp] at hP0; exact maxL_mem hP0
  have hfrP : ∀ f, f ∈ fr (.M m) q → ∃ p, P0 = some p ∧ Le f p := by
    intro f hf
    have hf' : f ∈ frB (.Xi m q) (.Xi m q) := by rw [frB_eq_fr]; exact (fr_rho_iff hρ).mpr hf
    cases P0 with
    | none => exact absurd (maxL_none hP0) (List.ne_nil_of_mem hf')
    | some p =>
      refine ⟨p, rfl, maxL_le (fun x hx => ?_) hP0 f hf'⟩
      rw [frB_eq_fr] at hx; exact (fr_elem hρ hx).1
  intro v hv hvF hvρ
  by_cases hq0 : q = .zero
  · subst hq0
    simp only [subs, List.mem_singleton] at hv
    rw [hv]; exact h0f
  by_cases hs : isSucc q = true
  · -- `q = q' + 1`：`v < Ξ_m(q') ≤ s < y_0`
    have hpF := predT_WNF hqF hs
    have hyF := xi_pred_wnf hρ hs
    have hyρ := xi_pred_lt hρ hs
    have hqe : succT (predT q) = q := succT_predT hqF hs
    have hPq : ∀ p, P0 = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true := fun p hp => by
      obtain ⟨h1, h2, h3, -, -⟩ := fr_elem hρ (hPe p hp); exact ⟨h1, h2, h3⟩
    obtain ⟨s, hs_def⟩ : ∃ s, s = maxO P0 (.Xi m (predT q)) := ⟨_, rfl⟩
    obtain ⟨hsF, hys', hPs, hcase⟩ := maxO_spec (P := P0) hyF (fun p hp => (hPq p hp).1)
    rw [← hs_def] at hsF hys' hPs hcase
    have hsρ : Lt s (.Xi m q) := by
      rcases hcase with e | ⟨p, hp, e⟩
      · rw [e]; exact hyρ
      · rw [e]; exact (hPq p hp).2.1
    have hsp' : isPrincipal s = true := by
      rcases hcase with e | ⟨p, hp, e⟩
      · rw [e]; rfl
      · rw [e]; exact (hPq p hp).2.2
    have hsM : Lt s (.M m) := lt_transY hsF hρ hMF hsρ hρM
    -- `s < y_0`
    have hsf : Lt s (mahloVK m q (info q).sums (.Xi m q) P0).first := by
      obtain ⟨ys, hys⟩ := summands_of_isSucc hs
      have hsp : summands (predT q) = ys := summands_predT hqF hys
      have hdl : (summands q).dropLast = ys := by rw [hys, List.dropLast_concat]
      have hpred : pred q = predT q := rfl
      unfold mahloVK
      rw [ite_eq_right hq0, ite_eq_left hs]
      simp only [hpred, ← hs_def]
      cases hsplit : splitPosD (.Xi m q) (info q).sums.dropLast with
      | none => exact tower_lt_succ hsF 0
      | some val =>
        obtain ⟨pre, R, r⟩ := val
        obtain ⟨rest, hsd, hr, hρR, -⟩ := splitPosD_spec hqF hρ hsplit
        subst hr
        have hsq : summands q = pre ++ R :: (rest ++ [one]) := by
          rw [hys, ← hdl, hsd]; simp
        have hRq : R ∈ summands q := by rw [hsq]; simp
        have hRW := summands_WNF q hqF R hRq
        have hsR : Lt s R := lt_of_lt_of_leY hsF hρ hRW.1 hsρ hρR
        simp only [mkApp_xi (ltB_iff.mpr hsR)]
        have G : XG m q s pre (rest ++ [one]) R := ⟨hρ, hsq, hsF, hsR, hsM, Or.inr hsp'⟩
        have hRS : R ≠ succM m := fun e => by
          have h1 : Le R q := le_of_mem_summands hqF hRq
          have h2 : Le q (succM m) := le_of_ne_gtY hqF hSF hle
          rw [e] at h1
          have h3 := le_antisymmY hqF hSF h2 h1
          rw [h3] at hs
          exact not_isSucc_succM m hs
        obtain ⟨A₀, hA₀, -, hPA, -⟩ :=
          app_first_xi G (hRinv R hRq) (not_succ_of_gt hsF hsp' hRW.2 hsR) hRS
        rw [hA₀]; exact hPA
    have hyfst : Lt (.Xi m (predT q)) (mahloVK m q (info q).sums (.Xi m q) P0).first :=
      lt_of_le_of_ltY hyF hsF hfF hys' hsf
    by_cases hq1 : predT q = .zero
    · have hq1' : q = one := by rw [← hqe, hq1]; rfl
      rw [hq1'] at hv
      exact lt_of_sub_one h1f hOf h0f hv
    have hv' : Lt v (.Xi m (predT q)) := by
      refine floor_lowx hρ hyF (fun f hf => ?_) (fun k a hn haq => ?_) (fun m' b hn hbq => ?_)
        v hv hvρ
      · rw [← hqe] at hf
        obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
        rw [summands_succT] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact k2xY hyF f (mem_fr_iff.mpr ⟨u, hu, hfu⟩)
        · rw [List.mem_singleton.mp hu] at hfu
          have hf1 : f = one := by
            rcases mem_subs_one (fr_spec hfu).1 with e | e | e
            · exact e
            · exfalso; rw [e] at hfu; rcases fr_node hfu with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
            · exfalso; rw [e] at hfu; rcases fr_node hfu with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
          rw [hf1]; exact one_lt_xi hyF
      · rw [← hqe] at hn
        rcases node_sub_succT (Or.inr ⟨k, a, rfl⟩) hn with hn' | hn'
        · have haF := (hpF.of_mem_subs hn').psi.aF
          have hsz : a.size < (predT q).size := by
            have := size_le_of_mem_subs hn'; simp only [Tm.size] at this; omega
          rcases le_of_lt_succT haF hpF (by rw [hqe]; exact haq) with e | h
          · exact absurd e (ne_of_size_lt hsz)
          · exact h
        · have ha0 : a = .zero := (Tm.Psi.inj hn').2
          rw [ha0]; exact zero_lt hq1
      · rw [← hqe] at hn
        rcases node_sub_succT (Or.inl ⟨m', b, rfl⟩) hn with hn' | hn'
        · have hbF := (hpF.of_mem_subs hn').xi.2.1
          have hsz : b.size < (predT q).size := by
            have := size_le_of_mem_subs hn'; simp only [Tm.size] at this; omega
          rcases le_of_lt_succT hbF hpF (by rw [hqe]; exact hbq) with e | h
          · exact absurd e (ne_of_size_lt hsz)
          · exact h
        · exact absurd hn' (by unfold one; intro e; cases e)
    exact lt_transY hvF hyF hfF hv' hyfst
  -- `q` 極限
  by_cases hqS : q = succM m
  · have hv0 : v ∈ (Tm.Om (.plus (.M m) one)) :: ((Tm.plus (.M m) one) :: ((Tm.M m) :: subs one)) := by
      rw [hqS] at hv; exact hv
    have hpl := hSF.om.1
    have hρMS : Lt (.Xi m q) (.plus (.M m) one) := lt_transY hρ hMF hpl hρM (lt_plus_leftY hpl)
    simp only [List.mem_cons] at hv0
    rcases hv0 with e | e | e | hv1
    · exfalso; rw [e] at hvρ
      exact Lt.asymmY hρ hSF (lt_transY hρ hMF hSF hρM (M_lt_succM hm)) hvρ
    · exfalso; rw [e] at hvρ; exact Lt.asymmY hρ hpl hρMS hvρ
    · exfalso; rw [e] at hvρ; exact Lt.asymmY hρ hMF hρM hvρ
    · exact lt_of_sub_one h1f hOf h0f hv1
  obtain ⟨R, x0, hsq, hfirst, hx0, hx0R, hgap, hpos, -, hY0F, -⟩ := s0_first_xi hρ hq0 hs hqS hRinv
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRW := summands_WNF q hqF R hRq
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have e0 : xa (summands q).dropLast .zero x0 = oadd (ofSummands (summands q).dropLast) x0 := by
    show oadd _ (nsum .zero x0) = _; rw [zero_nsum _ hx0]
  -- 節点の引数（`argCond`）
  have hcA : ∀ s, s ∈ summands q → ∀ a, a ∈ subs s → a ≠ s → Lt a q →
      Lt a (xa (summands q).dropLast .zero x0) := fun s hs' a has hne haq => by
    rw [e0]; exact argCond hqF hsq hx0 hgap hpos s hs' a has hne haq
  have hc1 : ∀ k a, Tm.Psi k a ∈ subs q → Lt a q → Lt a (xa (summands q).dropLast .zero x0) := by
    intro k a hn haq
    obtain ⟨s, hs', hns⟩ := node_mem_summand (Or.inr ⟨k, a, rfl⟩) hn
    exact hcA s hs' a (subs_trans hns (subs_psi_a (self_mem_subs a)))
      (ne_of_size_lt (by have := size_le_of_mem_subs hns; simp only [Tm.size] at this ⊢; omega)) haq
  have hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b (xa (summands q).dropLast .zero x0) := by
    intro m' b hn hbq
    obtain ⟨s, hs', hns⟩ := node_mem_summand (Or.inl ⟨m', b, rfl⟩) hn
    exact hcA s hs' b (subs_trans hns (mem_subs_xi m' b))
      (ne_of_size_lt (by have := size_le_of_mem_subs hns; simp only [Tm.size] at this ⊢; omega)) hbq
  have hGY : (∀ f, f ∈ fr (.M m) q → Lt f (.Xi m (xa (summands q).dropLast .zero x0))) →
      Lt v (.Xi m (xa (summands q).dropLast .zero x0)) := fun hF =>
    floor_lowx hρ hY0F hF hc1 hc1x v hv hvρ
  -- 最後の加数 `R = p`（前線の元）の真の部分項で `ρ` 未満のものは `Y0` 未満
  have hS' : ∀ p, P0 = some p → R = p → ∀ w, w ∈ subs p → w ≠ p → Lt w (.Xi m q) →
      Lt w (.Xi m (xa (summands q).dropLast .zero x0)) := by
    intro p hp hRp w hw hne hwρ
    obtain ⟨hpF, hpρ, -, -, -⟩ := fr_elem hρ (hPe p hp)
    have hwF := hpF.of_mem_subs hw
    have hsz := size_lt_of_mem_subs_ne hw hne
    have hpq : p ∈ summands q := by rw [← hRp]; exact hRq
    have hpsz := size_le_of_mem_subs (mem_subs_of_mem_summands hpq)
    have hRM : Lt R (.M m) := by rw [hRp]; exact lt_transY hpF hρ hMF hpρ hρM
    have hx0y : Lt x0 (.Xi m (xa (summands q).dropLast .zero x0)) :=
      coll_xi0 hY0F x0 hx0 (G0.parts hx0 hx0R (xi_selfY hY0F)).2.2 (lt_transY hx0 hRW.1 hMF hx0R hRM)
    have hfp : ∀ f, f ∈ fr (.M m) q → Le f p := fun f hf => by
      obtain ⟨p', hp', hfp'⟩ := hfrP f hf; rw [hp] at hp'; cases hp'; exact hfp'
    refine hull_ltx hρ hY0F (by simp only [Tm.size]; omega) (fun n hn hnF hny f hf => ?_)
      (fun k a hn haq => ?_) (fun m' b hn hbq => ?_) hwF (lt_transY hwF hρ hMF hwρ hρM)
      (inC_of_ltY q hwF hρ hwρ)
    · have hnp : n ∈ subs p := subs_trans hw hn
      have hnne : n ≠ p := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hn) hsz)
      have h1 : ¬ Lt n p := fun h' => hny (lt_transY hnF hx0 hY0F
        (hgap n (by rw [hRp]; exact hnp) (by rw [hRp]; exact hnne) (by rw [hRp]; exact h')) hx0y)
      have h2 : Lt p n := (le_of_not_ltY hnF hpF h1).resolve_left (Ne.symm hnne)
      exact lt_of_le_of_ltY (fr_elem hqF hf).1 hpF hnF (hfp f hf) h2
    · have hn' : Tm.Psi k a ∈ subs R := by rw [hRp]; exact subs_trans hw hn
      exact hcA R hRq a (subs_trans hn' (subs_psi_a (self_mem_subs a)))
        (ne_of_size_lt (by have := size_le_of_mem_subs hn'; simp only [Tm.size] at this ⊢; omega)) haq
    · have hn' : Tm.Xi m' b ∈ subs R := by rw [hRp]; exact subs_trans hw hn
      exact hcA R hRq b (subs_trans hn' (mem_subs_xi m' b))
        (ne_of_size_lt (by have := size_le_of_mem_subs hn'; simp only [Tm.size] at this ⊢; omega)) hbq
  unfold mahloVK
  rw [ite_eq_right hq0, ite_eq_right hs]
  dsimp only
  cases P0 with
  | none =>
    rw [hfirst]
    exact hGY (fun f hf => by obtain ⟨p, hp, -⟩ := hfrP f hf; cases hp)
  | some p =>
    dsimp only
    obtain ⟨hpF, hpρ, hpp, hp0, -⟩ := fr_elem hρ (hPe p rfl)
    have hpm := hPe p rfl
    have hfp : ∀ f, f ∈ fr (.M m) q → Le f p := fun f hf => by
      obtain ⟨p', hp', hfp'⟩ := hfrP f hf; cases hp'; exact hfp'
    by_cases h1 : ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
        (lastS (info q).sums) .zero .zero).first = true
    · rw [ite_eq_left h1, hfirst]
      rw [hfirst] at h1
      exact hGY (fun f hf => lt_of_le_of_ltY (fr_elem hqF hf).1 hpF hY0F (hfp f hf) (ltB_iff.mp h1))
    rw [ite_eq_right h1]
    by_cases h2 : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
        (lastS (info q).sums) .zero .zero).first = p
    · exact (floor_first_ne hρ hq0 hs hRinv hpm h2).elim
    rw [ite_eq_right h2]
    rw [hfirst] at h1 h2
    have hlt : Lt (.Xi m (xa (summands q).dropLast .zero x0)) p := by
      rcases triY hY0F hpF with h | e | h
      · exact h
      · exact absurd e h2
      · exact absurd (ltB_iff.mpr h) h1
    obtain ⟨-, hpleR, hpre⟩ := floor_tail hρ hsq hpm hx0 hx0R hY0F hlt
    cases hsg : splitGtD p (info q).sums with
    | none =>
      -- `q = p`、列は `p` の上の塔
      simp only
      have hall := splitGtD_none hqF hpF hsg
      have hRp : R = p := le_antisymmY hRW.1 hpF (hall R hRq) hpleR
      have hpre0 : (summands q).dropLast = [] := by
        cases hdl : (summands q).dropLast with
        | nil => rfl
        | cons u l =>
          exfalso
          have hu : u ∈ (summands q).dropLast := by rw [hdl]; simp
          have huq : u ∈ summands q := by rw [hsq]; exact List.mem_append_left _ hu
          exact not_lt_of_leY (summands_WNF q hqF u huq).1 hpF (hall u huq) (hpre u hu)
      have hqp : q = p := by
        have hsqp : summands q = [p] := by rw [hsq, hpre0, hRp]; rfl
        rw [← ofSummands_summands q hqF, hsqp]; rfl
      have hvp : v ∈ subs p := by rw [← hqp]; exact hv
      have hpt : Lt p (FS.tower p 1) := tower_lt_succ hpF 0
      show Lt v (FS.tower p 1)
      by_cases hvpe : v = p
      · rw [hvpe]; exact hpt
      · exact lt_transY hvF hY0F (wnf_tower hpF 1) (hS' p rfl hRp v hvp hvpe hvρ)
          (lt_transY hY0F hpF (wnf_tower hpF 1) hlt hpt)
    | some val =>
      -- `R₂ > p` で分ける
      obtain ⟨pre₂, R₂, r₂⟩ := val
      obtain ⟨rest₂, hsq₂, hr₂, hpR₂, hrest₂⟩ := splitGtD_spec hqF hpF hsg
      subst hr₂
      simp only [mkApp_xi (ltB_iff.mpr hpR₂)]
      have hR₂q : R₂ ∈ summands q := by rw [hsq₂]; simp
      have hR₂W := summands_WNF q hqF R₂ hR₂q
      have G₂ : XG m q p pre₂ rest₂ R₂ :=
        ⟨hρ, hsq₂, hpF, hpR₂, lt_transY hpF hρ hMF hpρ hρM, Or.inr hpp⟩
      have hR₂S : R₂ ≠ succM m := fun e => by
        have h3 : Le R₂ q := le_of_mem_summands hqF hR₂q
        have h4 : Le q (succM m) := le_of_ne_gtY hqF hSF hle
        rw [e] at h3
        exact hqS (le_antisymmY hqF hSF h4 h3)
      obtain ⟨A₀, hA₀, hyF₀, hpy₀, hc₀⟩ :=
        app_first_xi G₂ (hRinv R₂ hR₂q) (not_succ_of_gt hpF hpp hR₂W.2 hpR₂) hR₂S
      rw [hA₀]
      refine lt_of_summands_sub hρ rfl (zero_lt (by intro e; cases e)) hqF
        (fun s hs' w hw hwF hwρ => ?_) v hv hvF hvρ
      have hsq' := hs'
      rw [hsq₂] at hs'
      have hsF := (summands_WNF q hqF s hsq').1
      have hwsz : w.size ≤ s.size := size_le_of_mem_subs hw
      have hssz := size_le_of_mem_subs (mem_subs_of_mem_summands hsq')
      -- `pre₂ ++ [R₂]` の加数：`y_0 = Ξ_m(A₀)` への移し替え
      have hhull : s ∈ pre₂ ++ [R₂] → Lt w (.Xi m A₀) := fun hsP =>
        hull_ltx hρ hyF₀ (by simp only [Tm.size]; omega)
          (fun n _ hnF hny f hf => lt_of_le_of_ltY (fr_elem hqF hf).1 hpF hnF (hfp f hf)
            (lt_of_lt_of_leY hpF hyF₀ hnF hpy₀ (le_of_not_ltY hnF hyF₀ hny)))
          (fun k a hn haq => hc₀ s hsP a (subs_trans hw (subs_trans hn (subs_psi_a (self_mem_subs a))))
            (ne_of_size_lt (by have := size_le_of_mem_subs hn; simp only [Tm.size] at this ⊢; omega))
            haq)
          (fun m' b hn hbq => hc₀ s hsP b (subs_trans hw (subs_trans hn (mem_subs_xi m' b)))
            (ne_of_size_lt (by have := size_le_of_mem_subs hn; simp only [Tm.size] at this ⊢; omega))
            hbq)
          hwF (lt_transY hwF hρ hMF hwρ hρM) (inC_of_ltY q hwF hρ hwρ)
      rcases List.mem_append.mp hs' with hs'' | hs''
      · exact hhull (List.mem_append_left _ hs'')
      rcases List.mem_cons.mp hs'' with e | hs'''
      · exact hhull (by rw [e]; simp)
      · -- 後ろの加数は `p`（`= R`）
        have hRs : Le R s := by
          rw [hsq] at hsq'
          rcases List.mem_append.mp hsq' with h | h
          · exact le_of_ne_gtY hRW.1 hsF (nfl_append_ge G0.hNT s h R (by simp))
          · rw [List.mem_singleton.mp h]; exact Or.inl rfl
        have hsp : s = p := le_antisymmY hsF hpF (hrest₂ s hs''') (le_transY hpF hRW.1 hsF hpleR hRs)
        have hRp : R = p := le_antisymmY hRW.1 hpF (by rw [← hsp]; exact hRs) hpleR
        rw [hsp] at hw
        by_cases hwp : w = p
        · rw [hwp]; exact hpy₀
        · exact lt_transY hwF hY0F hyF₀ (hS' p rfl hRp w hw hwp hwρ)
            (lt_transY hY0F hpF hyF₀ hlt hpy₀)

/-! ### 底の列の不変量 -/

/-- `q ∉ C(g, x)`（`q ≤ g`）なら、`x` は前線の最大元 `P0` 以下 -/
theorem floor_le_seed {m : Nat} {q x g : Tm} (hρ : WNF (.Xi m q)) (hx : WNF x) (hxM : Lt x (.M m))
    (hg : WNF g) (hqg : Le q g) (hnC : inC q g x = false) :
    ∃ p, maxL (frB (.Xi m q) (.Xi m q)) = some p ∧ Le x p := by
  have hqF := hρ.xi.2.1
  have hqC := hρ.xi.2.2.2
  have hMF := WNF.M' hρ.xi.1
  have hcon : (∀ f, f ∈ fr (.M m) q → Lt f x) → False := fun hall => by
    have h := (inC_fr (R := .M m) (g0 := q) (g := g) (d := x) q hqC
      (fun w hw hwM hwx => hwM (lt_transY (hqF.of_mem_subs hw) hx hMF hwx hxM))
      (fun v hv hvq => lt_of_lt_of_leY (hqF.of_mem_subs hv) hqF hg hvq hqg)).mpr
      (fun w hw => inC_of_lt_node (fr_node hw) (hall w hw))
    rw [h] at hnC; cases hnC
  have hmem : ∀ f, f ∈ fr (.M m) q → f ∈ frB (.Xi m q) (.Xi m q) := fun f hf => by
    rw [frB_eq_fr]; exact (fr_rho_iff hρ).mpr hf
  cases hP : maxL (frB (.Xi m q) (.Xi m q)) with
  | none =>
    exfalso; apply hcon; intro f hf
    have hf' := hmem f hf
    rw [maxL_none hP] at hf'; cases hf'
  | some p =>
    refine ⟨p, rfl, ?_⟩
    have hpm : p ∈ fr (.Xi m q) (.Xi m q) := by rw [← frB_eq_fr]; exact maxL_mem hP
    have hpF := (fr_elem hρ hpm).1
    rcases triY hx hpF with h | e | h
    · exact Or.inr h
    · exact Or.inl e
    · exfalso; apply hcon; intro f hf
      have hfp := maxL_le (fun y hy => by rw [frB_eq_fr] at hy; exact (fr_elem hρ hy).1) hP f (hmem f hf)
      exact lt_of_le_of_ltY (fr_elem hqF hf).1 hpF hx hfp h

/-- 底 `¬ q < X'`：`X = q + 1` -/
theorem floor_succ_eq {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X)) (hs : isSucc X = true)
    (hnv : ¬ Lt q (predT X)) : X = succT q := by
  have hP := ht.psi
  have hXF := hP.aF
  have hqF := hP.piF.xi.2.1
  have hqX : Lt q X := hP.act m q rfl
  rcases le_pred_of_lt_succ hXF hs hqF hqX with e | h
  · rw [e]; exact (succT_predT hXF hs).symm
  · exact absurd h hnv

theorem cs_succ_xi_floor {m : Nat} {q X : Tm} (hX : WNF X) (hs : isSucc X = true)
    (hv : validR (.Xi m q) (pred X) = false) :
    cs (.Xi m q) X = mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q))) := by
  have hX0 : X ≠ .zero := by intro e; rw [e] at hs; cases hs
  unfold cs cseq
  rw [ite_eq_right hX0, (lastS_dom_one_iff hX hX0).mpr hs]
  simp only [hv, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- 底の族の閉包（`ω` 型） -/
theorem famNat_floor {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).dom = .omega) :
    FamNat m q (maxL (frB (.Xi m q) (.Xi m q)))
      (fun n => (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).nat n) := by
  have hpm : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → p ∈ fr (.Xi m q) (.Xi m q) :=
    fun p hp => by rw [← frB_eq_fr]; exact maxL_mem hp
  have hP : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p →
      WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true := fun p hp => by
    obtain ⟨h1, h2, h3, -, -⟩ := fr_elem hρ (hpm p hp); exact ⟨h1, h2, h3⟩
  by_cases hq0 : q = .zero
  · subst hq0; exact famNat_vk_zero hρ hP
  by_cases hs : isSucc q = true
  · exact famNat_vk_succ hρ hs hRinv hP hdom
  · exact famNat_vk_lim hρ hq0 hs hRinv hP
      (fun p hp h1 h2 => seedHyp_floor hρ hq0 hs hRinv (hpm p hp) h1 h2)
      (fun p hp he => (floor_first_ne hρ hq0 hs hRinv (hpm p hp) he).elim) hdom

/-- 底の族の閉包（共終数が正則項） -/
theorem famBig_floor {m : Nat} {q σ : Tm} (hρ : WNF (.Xi m q)) (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).dom = .big σ) :
    FamBig m q (maxL (frB (.Xi m q) (.Xi m q))) σ
      (fun ξ => (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) := by
  have hpm : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → p ∈ fr (.Xi m q) (.Xi m q) :=
    fun p hp => by rw [← frB_eq_fr]; exact maxL_mem hp
  have hP : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p →
      WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true := fun p hp => by
    obtain ⟨h1, h2, h3, -, -⟩ := fr_elem hρ (hpm p hp); exact ⟨h1, h2, h3⟩
  by_cases hq0 : q = .zero
  · exfalso
    subst hq0
    unfold mahloVK at hdom
    rw [ite_eq_left rfl] at hdom
    exact tower_dom_ne_big _ _ hdom
  by_cases hs : isSucc q = true
  · exact famBig_vk_succ hρ hs hRinv hP hdom
  · exact famBig_vk_lim hρ hq0 hs hRinv hP
      (fun p hp h1 h2 => seedHyp_floor hρ hq0 hs hRinv (hpm p hp) h1 h2)
      (fun p hp he => (floor_first_ne hρ hq0 hs hRinv (hpm p hp) he).elim) hdom

/-- 底の共終性の一歩：`t = Ψ_ρ(q+1)` 未満で階 `m` の `Ξ_m(c)`（`q < c`）・`Ψ_κ(b)`（`κ ≥ ρ`）は種以下か
`M_{m-1}` 以下 -/
theorem floor_step {m : Nat} {q x : Tm} (ht : WNF (.Psi (.Xi m q) (succT q))) (hx : WNF x)
    (hxt : Lt x (.Psi (.Xi m q) (succT q))) :
    (∀ c, x = .Xi m c → Lt q c → inC q c (.Xi m c) = false →
      ∃ p, maxL (frB (.Xi m q) (.Xi m q)) = some p ∧ Le x p) ∧
    (∀ κ b, x = .Psi κ b → lev κ = m → ¬ Lt κ (.Xi m q) →
      (∃ p, maxL (frB (.Xi m q) (.Xi m q)) = some p ∧ Le x p) ∨ Le x (kTerm (m - 1))) := by
  have hP := ht.psi
  have hρ := hP.piF
  have hρT := hP.tgt
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hxρ : Lt x (.Xi m q) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
  have hxM : Lt x (.M m) := lt_transY hx hρ hMF hxρ hρM
  refine ⟨fun c e hqc hnC => ?_, fun κ b e hlκ hκρ => ?_⟩
  · subst e
    exact floor_le_seed hρ hx hxM hx.xi.2.1 (Or.inr hqc) hnC
  · subst e
    have hQ := hx.psi
    have hκF := hQ.piF
    rcases triY hκF hρ with h | e | hρκ
    · exact absurd h hκρ
    · exfalso
      subst e
      have hbX : Lt b (succT q) := lt_psi_psi_same.mp hxt
      exact not_lt_of_leY hQ.aF hqF (le_of_lt_succT hQ.aF hqF hbX) (hQ.act m q rfl)
    · have hnb := not_base_of_lt_tgtY hx hρ hρT hlκ hρκ hxρ
      by_cases hkx : Lt (kTerm (m - 1)) (.Psi κ b)
      · have hnC : inC q q (.Psi κ b) = false := by
          cases e : inC q q (.Psi κ b) with
          | false => rfl
          | true => rw [(baseOf_xi_iff m q _).mpr ⟨hkx, e⟩] at hnb; cases hnb
        exact Or.inl (floor_le_seed hρ hx hxM hqF (Or.inl rfl) hnC)
      · exact Or.inr (le_of_not_ltY (wnf_kTerm _) hx hkx)

/-- `predT (q + 1) = q` -/
theorem predT_succT_eq {q : Tm} (hq : WNF q) : predT (succT q) = q := by
  have hs := succT_WNF hq
  exact eq_of_summands_eq (predT_WNF hs (isSucc_succT q)) hq (summands_predT hs (summands_succT q))

/-- `Ψ_{Ξ_m(q)}(q+1)` の列が `ω` 型なら、その不変量 -/
theorem natInv_psi_succ_xi_floor {m : Nat} {q : Tm} (ht : WNF (.Psi (.Xi m q) (succT q)))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) (succT q)).size → WNF u → Inv u)
    (hdom : dom (.Psi (.Xi m q) (succT q)) = .omega) : NatInv (.Psi (.Xi m q) (succT q)) := by
  have hP := ht.psi
  have hρ := hP.piF
  have hXF := hP.aF
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hs : isSucc (succT q) = true := isSucc_succT q
  have hX0 : succT q ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hv : validR (.Xi m q) (pred (succT q)) = false := by
    cases e : validR (.Xi m q) (pred (succT q)) with
    | false => rfl
    | true =>
      exfalso
      have h1 : Lt q (predT (succT q)) := ltB_iff.mp e
      rw [predT_succT_eq hqF] at h1
      exact Lt.irrefl _ h1
  have hcs := cs_succ_xi_floor hXF hs hv
  have hfN : ∀ n, fundNat (.Psi (.Xi m q) (succT q)) n =
      (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).nat n := by
    intro n; rw [fundNat_psi, hcs]
  have hdom' : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).dom = .omega := by
    rw [← hcs, ← dom_psi]; exact hdom
  have hRinv : ∀ R, R ∈ summands q → Inv R := by
    intro R hR
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  have F := famNat_floor hρ hRinv hdom'
  have hpm : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → p ∈ fr (.Xi m q) (.Xi m q) :=
    fun p hp => by rw [← frB_eq_fr]; exact maxL_mem hp
  have hpF : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → WNF p := fun p hp =>
    (fr_elem hρ (hpm p hp)).1
  obtain ⟨-, hqt⟩ := (baseOf_xi_iff m q _).mp (base_selfY ht)
  have hqXlt : Lt q (succT q) := lt_succT q
  have hqCt : inC q (succT q) (.Psi (.Xi m q) (succT q)) = true :=
    inC_mono q q _ (succT q) _ hqt (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq hqXlt)
  have hρCt : inC (.Xi m q) (succT q) (.Psi (.Xi m q) (succT q)) = true :=
    inC_xi_iff.mpr (Or.inr ⟨hqCt, hqXlt⟩)
  have hρt : ¬ Lt (.Xi m q) (.Psi (.Xi m q) (succT q)) := Lt.asymmY ht hρ (lt_psi_targetY ht)
  have hcutt := Cut.of_wnf ht
  have hyt : ∀ n, Lt ((mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).nat n)
      (.Psi (.Xi m q) (succT q)) := by
    intro n
    have hyC := F.ub (succT q) _ n hXF hX0 hcutt hρCt hρt (fun p hp =>
      inC_of_lt_cut hcutt _ (hpF p hp) (k2tY ht p (hpm p hp)))
    exact coll_psiY ht (F.F n) hyC (F.ltρ n)
  -- 隙間：列の 0 番目
  have hfirst : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first =
      (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).nat 0 := by
    unfold SeqD.first; rw [hdom']
  have hy0F : WNF (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first := by
    rw [hfirst]; exact F.F 0
  obtain ⟨h1f, hOf, h0f, hpf⟩ := mahloVK_first_big hy0F
  have hgq := floor_gap hρ hRinv hy0F
  have hgapt := gp_floor ht (subs_xi (self_mem_subs q)) hpf h1f hOf h0f (fun v hv hvF hvρ => by
    have hv' : v = .Xi m q ∨ v ∈ subs q := by simpa only [subs, List.mem_cons] using hv
    rcases hv' with e | hv'
    · rw [e] at hvρ; exact absurd hvρ (Lt.irrefl _)
    · exact hgq v hv' hvF hvρ)
  -- 共終性
  have hcof : ∀ x, WNF x → Lt x (.Psi (.Xi m q) (succT q)) →
      ∃ n, Lt x ((mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).nat n) := by
    refine cof_nat (t := .Psi (.Xi m q) (succT q)) F.F F.mono (fun x hx hxt N hN => ?_)
    obtain ⟨hstX, hstP⟩ := floor_step ht hx hxt
    have hlev : lev x ≤ m := by have := lev_le_of_lt_gen hxt; simpa [lev] using this
    rcases Nat.lt_or_eq_of_le hlev with hl | hl
    · exact ⟨0, lt_y0_of_lev F hm hx hl⟩
    cases x with
    | zero => exfalso; simp only [lev] at hl; omega
    | M j =>
      refine ⟨0, lt_of_le_of_ltY hx (wnf_kTerm _) (F.F 0) ?_ F.bot⟩
      simp only [lev] at hl
      unfold kTerm
      rw [ite_eq_right (by have := hx.M; omega)]
      have : j = m - 1 := by omega
      rw [this]; exact Or.inl rfl
    | plus a b =>
      obtain ⟨ha, -, -, -⟩ := hx.plus
      have h1 := hN a (by simp [parL, parF]) (lt_transY ha hx ht (lt_plus_leftY hx) hxt)
      exact ⟨N, (lt_plus_prin_iffY hx (F.prin N)).mpr h1⟩
    | Om e =>
      have heF := hx.om.1
      exact F.om e N heF (hN e (by simp [parL, parF]) (lt_transY heF hx ht (lt_om_selfY hx) hxt))
    | Xi j c =>
      simp only [lev] at hl
      subst hl
      obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := .Xi j q) (γ := succT q) (f := c) (n := j) rfl).mp hxt
      have hxρ : Lt (.Xi j c) (.Xi j q) := lt_of_gtY hρ hx hgt
      have hne : c ≠ q := fun e => by rw [e] at hxρ; exact Lt.irrefl _ hxρ
      rcases (lt_xi_xi0 hne).mp hxρ with ⟨hcq, -⟩ | ⟨hqc, hnC⟩
      · exact F.clo c N hx hxρ hcq (fun w hw => hN w hw
          (lt_transY (hx.xi.2.1.of_mem_subs (fr_spec hw).1) hx ht (k2xY hx w hw) hxt))
      · obtain ⟨p, hp, hxp⟩ := hstX c rfl hqc hnC
        exact ⟨0, lt_of_le_of_ltY hx (hpF p hp) (F.F 0) hxp (F.seed p hp)⟩
    | Psi κ b =>
      have hQ := hx.psi
      have hκF := hQ.piF
      have hlκ : lev κ = m := by simpa [lev] using hl
      by_cases hκρ : Lt κ (.Xi m q)
      · have h1 := tgt_lt_of_psi_lt hx ht hκρ hxt
        have h2 := hN κ (by simp [parL]) h1
        exact ⟨N, lt_transY hx hκF (F.F N) (lt_psi_targetY hx) h2⟩
      · rcases hstP κ b rfl hlκ hκρ with ⟨p, hp, hxp⟩ | h
        · exact ⟨0, lt_of_le_of_ltY hx (hpF p hp) (F.F 0) hxp (F.seed p hp)⟩
        · exact ⟨0, lt_of_le_of_ltY hx (wnf_kTerm _) (F.F 0) h F.bot⟩
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC => ?_, fun n v hv hne hvt => ?_, fun g d n hg hg0 hd hC => ?_⟩
  · rw [hfN]; exact F.F n
  · rw [hfN]; exact hyt n
  · rw [hfN, hfN]; exact F.mono n
  · obtain ⟨n, hn⟩ := hcof x hx hxt
    exact ⟨n, by rw [hfN]; exact Or.inr hn⟩
  · rw [hfN]; intro e; have := F.prin n; rw [e] at this; cases this
  · -- 上界
    rw [hfN]
    by_cases hlt : Lt (.Psi (.Xi m q) (succT q)) d
    · exact inC_of_lt_cut hd g (F.F n) (hd _ _ (F.F n) ht (hyt n) hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, -, -⟩
    · exact absurd h1 hlt
    have hρd : ¬ Lt (.Xi m q) d := fun h' => hlt (hd _ _ ht hρ (lt_psi_targetY ht) h')
    refine F.ub g d n hg hg0 hd hρC hρd (fun p hp => ?_)
    by_cases hpd : Lt p d
    · exact inC_of_lt_cut hd g (hpF p hp) hpd
    · exact fr_inC_of_tgt hρ (Or.inr (Or.inr ⟨m, q, rfl⟩)) hg hd hρC hρd p (hpm p hp)
  · -- 隙間
    rw [hfN]
    have h1 := hgapt v hv hne hvt
    rw [hfirst] at h1
    exact lt_of_lt_of_leY (ht.of_mem_subs hv) (F.F 0) (F.F n) h1 (F.mono_le (Nat.zero_le n))
  · rw [hfN] at hC ⊢; exact F.ub2 g d n hg hg0 hd hC

/-- `Ψ_{Ξ_m(q)}(q+1)` の列の共終数が正則項 `σ` なら、その不変量 -/
theorem bigInv_psi_succ_xi_floor {m : Nat} {q σ : Tm} (ht : WNF (.Psi (.Xi m q) (succT q)))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) (succT q)).size → WNF u → Inv u)
    (hdom : dom (.Psi (.Xi m q) (succT q)) = .big σ) : BigInv (.Psi (.Xi m q) (succT q)) σ := by
  have hP := ht.psi
  have hρ := hP.piF
  have hXF := hP.aF
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hs : isSucc (succT q) = true := isSucc_succT q
  have hX0 : succT q ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hv : validR (.Xi m q) (pred (succT q)) = false := by
    cases e : validR (.Xi m q) (pred (succT q)) with
    | false => rfl
    | true =>
      exfalso
      have h1 : Lt q (predT (succT q)) := ltB_iff.mp e
      rw [predT_succT_eq hqF] at h1
      exact Lt.irrefl _ h1
  have hcs := cs_succ_xi_floor hXF hs hv
  have hfB : ∀ ξ, fundBig (.Psi (.Xi m q) (succT q)) ξ =
      (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).big ξ := by
    intro ξ; rw [fundBig_psi, hcs]
  have hdom' : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).dom = .big σ := by
    rw [← hcs, ← dom_psi]; exact hdom
  have hRinv : ∀ R, R ∈ summands q → Inv R := by
    intro R hR
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  have F := famBig_floor hρ hRinv hdom'
  have hpm : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → p ∈ fr (.Xi m q) (.Xi m q) :=
    fun p hp => by rw [← frB_eq_fr]; exact maxL_mem hp
  have hpF : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → WNF p := fun p hp =>
    (fr_elem hρ (hpm p hp)).1
  obtain ⟨-, hqt⟩ := (baseOf_xi_iff m q _).mp (base_selfY ht)
  have hqXlt : Lt q (succT q) := lt_succT q
  have hqCt : inC q (succT q) (.Psi (.Xi m q) (succT q)) = true :=
    inC_mono q q _ (succT q) _ hqt (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq hqXlt)
  have hρCt : inC (.Xi m q) (succT q) (.Psi (.Xi m q) (succT q)) = true :=
    inC_xi_iff.mpr (Or.inr ⟨hqCt, hqXlt⟩)
  have hρt : ¬ Lt (.Xi m q) (.Psi (.Xi m q) (succT q)) := Lt.asymmY ht hρ (lt_psi_targetY ht)
  have hcutt := Cut.of_wnf ht
  -- `σ` の位置
  have hσF := F.σF
  have hσ0 := F.pos
  have hσt : Lt σ (.Psi (.Xi m q) (succT q)) :=
    coll_psiY ht hσF (F.σC (succT q) _ hcutt hqCt) F.σρ
  have hbF := wnf_base hσF F.σreg
  have hbσ := base_lt hσF F.σreg
  have hy0F := F.F .zero WNF.zero hσ0
  have hyt : ∀ ξ, WNF ξ → Lt ξ σ → Lt ((mahloVK m q (info q).sums (.Xi m q)
      (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) (.Psi (.Xi m q) (succT q)) := by
    intro ξ hξ hξσ
    have hyC := F.ub (succT q) _ ξ hXF hX0 hcutt hξ hξσ
      (inC_of_lt_cut hcutt _ hbF (lt_transY hbF hσF ht hbσ hσt)) hρCt hρt
      (fun p hp => inC_of_lt_cut hcutt _ (hpF p hp) (k2tY ht p (hpm p hp)))
      (inC_of_lt_cut hcutt _ hξ (lt_transY hξ hσF ht hξσ hσt))
    exact coll_psiY ht (F.F ξ hξ hξσ) hyC (F.ltρ ξ hξ hξσ)
  -- `M_k`（`σ = M_k`）は列の下
  have hMy : ∀ k, σ = .M k → ∀ ξ, WNF ξ → Lt ξ σ → Lt (.M k) ((mahloVK m q (info q).sums (.Xi m q)
      (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) := by
    intro k e ξ hξ hξσ
    have hkF : WNF (.M k) := by rw [← e]; exact hσF
    have hk1 : 1 ≤ k := hkF.M
    have hkρ : Lt (.M k) (.Xi m q) := by rw [← e]; exact F.σρ
    have hlk : k + 1 ≤ m := by have := lev_le_of_lt_gen hkρ; simpa [lev] using this
    have hle : Le (.M k) (kTerm (m - 1)) := by
      unfold kTerm
      rw [ite_eq_right (by omega)]
      rcases Nat.lt_or_eq_of_le (show k ≤ m - 1 by omega) with h | h
      · exact Or.inr (lt_of_lev_lt' (by simp only [lev]; omega))
      · rw [h]; exact Or.inl rfl
    exact lt_of_lt_of_leY hkF hy0F (F.F ξ hξ hξσ)
      (lt_of_le_of_ltY hkF (wnf_kTerm _) hy0F hle F.bot) (F.le0 hξ hξσ)
  -- 隙間：列の 0 番目
  have hfirst : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first =
      (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).big .zero := by
    unfold SeqD.first; rw [hdom']
  have hfF : WNF (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).first := by
    rw [hfirst]; exact hy0F
  obtain ⟨h1f, hOf, h0f, hpf⟩ := mahloVK_first_big hfF
  have hgq := floor_gap hρ hRinv hfF
  have hgapt := gp_floor ht (subs_xi (self_mem_subs q)) hpf h1f hOf h0f (fun v hv hvF hvρ => by
    have hv' : v = .Xi m q ∨ v ∈ subs q := by simpa only [subs, List.mem_cons] using hv
    rcases hv' with e | hv'
    · rw [e] at hvρ; exact absurd hvρ (Lt.irrefl _)
    · exact hgq v hv' hvF hvρ)
  have hgapS : ∀ ξ, WNF ξ → Lt ξ σ → ∀ v, v ∈ subs (Tm.Psi (.Xi m q) (succT q)) →
      v ≠ .Psi (.Xi m q) (succT q) → Lt v (.Psi (.Xi m q) (succT q)) →
      Lt v ((mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) := by
    intro ξ hξ hξσ v hv hne hvt
    have h1 := hgapt v hv hne hvt
    rw [hfirst] at h1
    exact lt_of_lt_of_leY (ht.of_mem_subs hv) hy0F (F.F ξ hξ hξσ) h1 (F.le0 hξ hξσ)
  -- 添字での共終性
  have hcloS : ∀ ξ, WNF ξ → Lt .zero ξ → Lt ξ σ → ∀ x, WNF x → Lt x (.Psi (.Xi m q) (succT q)) →
      (∀ f, f ∈ lfr σ x → Lt f ξ) → Lt x ((mahloVK m q (info q).sums (.Xi m q)
        (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) := by
    intro ξ hξ hξ0 hξσ x
    induction x using size_induction with
    | h x ih' =>
    intro hx hxt hfr
    have hyξ := F.F ξ hξ hξσ
    have hy0ξ := F.le0 hξ hξσ
    obtain ⟨hstX, hstP⟩ := floor_step ht hx hxt
    by_cases hxσ : Lt x σ
    · have h1 := hfr x (by rw [lfr_of_lt hxσ]; exact List.mem_singleton.mpr rfl)
      exact lt_transY hx hξ hyξ h1 (F.ge ξ hξ hξσ)
    have hpart : ∀ w, w ∈ parF x → Lt w ((mahloVK m q (info q).sums (.Xi m q)
        (maxL (frB (.Xi m q) (.Xi m q)))).big ξ) := fun w hw => by
      have hwx := parF_lt hx hw
      have hwF := hx.of_mem_subs (parF_mem_subs hw)
      refine ih' w (parL_sub (parF_sub_parL hw)).2 hwF (lt_transY hwF hx ht hwx hxt) (fun f hf => ?_)
      obtain ⟨g, hg, hfg⟩ := lfr_of_parF hσF hx hxσ hw hf
      exact lt_of_le_of_ltY (hwF.of_mem_subs (lfr_spec hf).1) (hx.of_mem_subs (lfr_spec hg).1)
        hξ hfg (hfr g hg)
    have hlev : lev x ≤ m := by have := lev_le_of_lt_gen hxt; simpa [lev] using this
    rcases Nat.lt_or_eq_of_le hlev with hl | hl
    · exact lt_of_lt_of_leY hx hy0F hyξ (lt_y0_of_lev_big F hm hx hl) hy0ξ
    cases x with
    | zero => exfalso; simp only [lev] at hl; omega
    | M j =>
      refine lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (wnf_kTerm _) hy0F ?_ F.bot) hy0ξ
      simp only [lev] at hl
      unfold kTerm
      rw [ite_eq_right (by have := hx.M; omega)]
      have : j = m - 1 := by omega
      rw [this]; exact Or.inl rfl
    | plus a b => exact (lt_plus_prin_iffY hx (F.prin ξ)).mpr (hpart a (by simp [parF]))
    | Om e => exact (lt_om_OFG (F.OF ξ) hyξ).mpr (hpart e (by simp [parF]))
    | Xi j c =>
      simp only [lev] at hl
      subst hl
      obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := .Xi j q) (γ := succT q) (f := c) (n := j) rfl).mp hxt
      have hxρ : Lt (.Xi j c) (.Xi j q) := lt_of_gtY hρ hx hgt
      have hne : c ≠ q := fun e => by rw [e] at hxρ; exact Lt.irrefl _ hxρ
      rcases (lt_xi_xi0 hne).mp hxρ with ⟨hcq, -⟩ | ⟨hqc, hnC⟩
      · exact F.clo c ξ hx hxρ hcq hξ hξ0 hξσ (fun f hf => hfr f ((mem_lfr_xi hxσ).mpr hf))
          (fun w hw => hpart w hw)
      · obtain ⟨p, hp, hxp⟩ := hstX c rfl hqc hnC
        exact lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (hpF p hp) hy0F hxp (F.seed p hp)) hy0ξ
    | Psi κ b =>
      have hQ := hx.psi
      have hκF := hQ.piF
      have hlκ : lev κ = m := by simpa [lev] using hl
      by_cases hκρ : Lt κ (.Xi m q)
      · have h1 := tgt_lt_of_psi_lt hx ht hκρ hxt
        have h2 := ih' κ (by simp only [Tm.size]; omega) hκF h1
          (fun f hf => hfr f ((mem_lfr_psi hxσ).mpr (Or.inl hf)))
        exact lt_transY hx hκF hyξ (lt_psi_targetY hx) h2
      · rcases hstP κ b rfl hlκ hκρ with ⟨p, hp, hxp⟩ | h
        · exact lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (hpF p hp) hy0F hxp (F.seed p hp))
            hy0ξ
        · exact lt_of_lt_of_leY hx hy0F hyξ (lt_of_le_of_ltY hx (wnf_kTerm _) hy0F h F.bot) hy0ξ
  refine {
    props := ⟨hσF, hσ0, fun ξ hξ hξσ => ?_, fun ξ hξ hξσ => ?_,
      fun ξ η hξ hη hξη hησ => ?_, fun x hx hxt => ?_⟩
    σreg := F.σreg
    σsub := subs_psi_p (subs_xi F.σsub)
    σle := Or.inr hσt
    pos := fun ξ hξ hξσ h0 => by rw [hfB] at h0; exact absurd h0 (F.ne_zero ξ)
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => by rw [hfB] at hC; exact F.lo g d ξ hd hξ hξσ hC
    ge := fun ξ hξ hξσ => by rw [hfB]; exact Or.inr (F.ge ξ hξ hξσ)
    gap := fun ξ v hξ hξσ hv hne hvt => by rw [hfB]; exact Or.inr (hgapS ξ hξ hξσ v hv hne hvt)
    gapP := fun _ ξ v hξ hξσ hv hne hvt => by rw [hfB]; exact hgapS ξ hξ hξσ v hv hne hvt
    lclo := fun x ξ hx hxt hξ hξ0 hξσ hfr => by rw [hfB]; exact hcloS ξ hξ hξ0 hξσ x hx hxt hfr
    nsucc := fun ξ hξ hξσ _ _ => by
      rw [hfB]
      obtain ⟨A, hA⟩ := F.xi ξ
      rw [hA]; simp [isSucc, summands, one]
    bge := fun ξ hξ hξσ => by rw [hfB]; exact Or.inr (F.blt ξ hξ hξσ)
    lbK := fun m' e _ ξ hξ hξσ => by rw [hfB]; exact Or.inr (hMy m' e ξ hξ hξσ)
    lbS := fun m' e _ ξ hξ hξσ => by
      rw [hfB]
      have hm' : 1 ≤ m' := by have h := hσF; rw [e] at h; exact h.M
      have hSF := WNF.succM hm'
      exact Or.inr ((lt_om_OFG (F.OF ξ) (F.F ξ hξ hξσ)).mpr
        ((lt_plus_prin_iffY hSF.om.1 (F.prin ξ)).mpr (hMy m' e ξ hξ hξσ)))
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      rw [hfB] at hC ⊢; exact F.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [hfB] at hC; exact F.bw g d ξ L hd hξ hξσ hL hσL hC }
  · rw [hfB]; exact F.F ξ hξ hξσ
  · rw [hfB]; exact hyt ξ hξ hξσ
  · rw [hfB, hfB]; exact F.mono ξ η hξ hη hξη hησ
  · obtain ⟨ξ, hξ, hξ0, hξσ, hl⟩ := exists_above hσF F.σreg hσ0 (lfr σ x)
      (fun f hf => ⟨hx.of_mem_subs (lfr_spec hf).1, (lfr_spec hf).2⟩)
    exact ⟨ξ, hξ, hξσ, by rw [hfB]; exact Or.inr (hcloS ξ hξ hξ0 hξσ x hx hxt hl)⟩
  · by_cases hlt : Lt (.Psi (.Xi m q) (succT q)) d
    · exact inC_of_lt_cut hd g hσF (hd _ _ hσF ht hσt hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, -, -⟩
    · exact absurd h1 hlt
    rcases inC_xi_iff.mp hρC with h2 | ⟨hqC', -⟩
    · exact inC_of_lt_cut hd g hσF (hd _ _ hσF hρ F.σρ h2)
    · exact F.σC g d hd hqC'
  · rw [hfB]
    by_cases hlt : Lt (.Psi (.Xi m q) (succT q)) d
    · exact inC_of_lt_cut hd g (F.F ξ hξ hξσ) (hd _ _ (F.F ξ hξ hξσ) ht (hyt ξ hξ hξσ) hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨hρC, -, -⟩
    · exact absurd h1 hlt
    have hρd : ¬ Lt (.Xi m q) d := fun h' => hlt (hd _ _ ht hρ (lt_psi_targetY ht) h')
    refine F.ub g d ξ hg hg0 hd hξ hξσ hbC hρC hρd (fun p hp => ?_) hξC
    by_cases hpd : Lt p d
    · exact inC_of_lt_cut hd g (hpF p hp) hpd
    · exact fr_inC_of_tgt hρ (Or.inr (Or.inr ⟨m, q, rfl⟩)) hg hd hρC hρd p (hpm p hp)

/-! ### まとめ -/

/-- `Ξ` への崩壊の後者の底の列の不変量 -/
theorem psiXiSuccFloor_proof : PsiXiSuccFloor := by
  intro n p X ht hs hnv ih
  have hXe := floor_succ_eq ht hs hnv
  subst hXe
  exact ⟨fun hd => natInv_psi_succ_xi_floor ht ih hd, fun _ hd => bigInv_psi_succ_xi_floor ht ih hd⟩

end MahloOCF.FS