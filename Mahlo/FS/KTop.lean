import Mahlo.FS.KCl

/-! `M_m` への対角化の塔の始点 `kTop`（目標の前線の、塔の障害の最大のもの）の仕様。

障害の探索 `kNd` の結果は、`z` の中にそれ以上の節点だけを通って見える（`selfVis`）節点なので、成分の所属
（`inC_of_selfVis`）を受け継ぐ。障害が `s` 以下の項（`KD`）は、`s` が塔の 1 段目より小さければ、塔の閉包の分解
（`xi_tower_hull`）で塔の下に入る（`kTop_hull`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### `kNd` の展開 -/

section
variable (m : Nat) (X : Tm)

theorem kNd_t_zero : kNd m X true .zero = none := by rw [kNd] <;> simp
theorem kNd_t_M (j : Nat) : kNd m X true (.M j) = none := by rw [kNd] <;> simp
theorem kNd_t_plus (a b : Tm) :
    kNd m X true (.plus a b) = maxOpt (kNd m X true a) (kNd m X true b) := by conv => lhs; rw [kNd]
theorem kNd_t_om (e : Tm) : kNd m X true (.Om e) = kNd m X true e := by conv => lhs; rw [kNd]
theorem kNd_t_psi (ρ a : Tm) :
    kNd m X true (.Psi ρ a) =
      (match kNd m X true ρ with
       | none => none
       | some u => some (if ltB u (.Psi ρ a) then u else .Psi ρ a)) := by
  conv => lhs; rw [kNd]
  rfl
theorem kNd_t_xi (j : Nat) (ζ : Tm) :
    kNd m X true (.Xi j ζ) =
      if j = m then
        (if ltB ζ X then
          (match kNd m X false ζ with
           | none => none
           | some u => some (if ltB u (.Xi j ζ) then u else .Xi j ζ))
        else some (.Xi j ζ))
      else none := by
  conv => lhs; rw [kNd]
  rfl
theorem kNd_f_zero : kNd m X false .zero = none := by rw [kNd] <;> simp
theorem kNd_f_M (j : Nat) : kNd m X false (.M j) = none := by rw [kNd] <;> simp
theorem kNd_f_plus (a b : Tm) :
    kNd m X false (.plus a b) = maxOpt (kNd m X false a) (kNd m X false b) := by conv => lhs; rw [kNd]
theorem kNd_f_om (e : Tm) : kNd m X false (.Om e) = kNd m X false e := by conv => lhs; rw [kNd]
theorem kNd_f_xi (j : Nat) (a : Tm) :
    kNd m X false (.Xi j a) =
      if ltB (.Xi j a) (.M m) then kNd m X true (.Xi j a) else kNd m X false a := by conv => lhs; rw [kNd]
theorem kNd_f_psi (p a : Tm) :
    kNd m X false (.Psi p a) =
      if ltB (.Psi p a) (.M m) then kNd m X true (.Psi p a)
      else maxOpt (kNd m X false p) (kNd m X false a) := by conv => lhs; rw [kNd]

end

/-! ### 探索の結果の性質 -/

/-- 探索の結果 `u` は `z` の中にそれ以上の節点だけを通って見え、`M_m` 未満。`top` なら `u ≤ z` -/
theorem kNd_spec {m : Nat} {X : Tm} (hm : 1 ≤ m) : ∀ (n : Nat) (top : Bool) (z u : Tm),
    2 * z.size + (if top then 0 else 1) ≤ n → WNF z → (top = true → Lt z (.M m)) →
    kNd m X top z = some u → selfVis u z = true ∧ Lt u (.M m) ∧ (top = true → Le u z) := by
  have hMF : WNF (.M m) := WNF.M' hm
  intro n
  induction n with
  | zero =>
    intro top z u hn
    have := Tm.size_pos z
    exfalso
    cases top <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  | succ n ih =>
    intro top z u hn hz hzM h
    cases top with
    | true =>
      have hzM' := hzM rfl
      simp only [↓reduceIte, Nat.add_zero] at hn
      cases z with
      | zero => rw [kNd_t_zero] at h; cases h
      | M j => rw [kNd_t_M] at h; cases h
      | plus a b =>
        rw [kNd_t_plus] at h
        obtain ⟨ha, hb, -, -⟩ := hz.plus
        simp only [Tm.size] at hn
        rcases maxOpt_cases h with h' | h'
        · have haM : Lt a (.M m) := lt_transY ha hz hMF (lt_plus_leftY hz) hzM'
          obtain ⟨h1, h2, h3⟩ := ih true a u (by simp only [↓reduceIte]; omega) ha (fun _ => haM) h'
          have huF := ha.of_mem_subs (selfVis_mem h1)
          exact ⟨by simp [selfVis, h1], h2,
            fun _ => le_transY huF ha hz (h3 rfl) (Or.inr (lt_plus_leftY hz))⟩
        · have hbM : Lt b (.M m) := lt_transY hb hz hMF (lt_plus_rightY hz) hzM'
          obtain ⟨h1, h2, h3⟩ := ih true b u (by simp only [↓reduceIte]; omega) hb (fun _ => hbM) h'
          have huF := hb.of_mem_subs (selfVis_mem h1)
          exact ⟨by simp [selfVis, h1], h2,
            fun _ => le_transY huF hb hz (h3 rfl) (Or.inr (lt_plus_rightY hz))⟩
      | Om e =>
        rw [kNd_t_om] at h
        have he := hz.om.1
        simp only [Tm.size] at hn
        have heM : Lt e (.M m) := lt_transY he hz hMF (lt_om_selfY hz) hzM'
        obtain ⟨h1, h2, h3⟩ := ih true e u (by simp only [↓reduceIte]; omega) he (fun _ => heM) h
        have huF := he.of_mem_subs (selfVis_mem h1)
        exact ⟨by simp [selfVis, h1], h2, fun _ => le_transY huF he hz (h3 rfl) (Or.inr (lt_om_selfY hz))⟩
      | Psi ρ a =>
        rw [kNd_t_psi] at h
        have hρF := hz.psi.piF
        simp only [Tm.size] at hn
        cases hρ : kNd m X true ρ with
        | none => rw [hρ] at h; cases h
        | some u' =>
          rw [hρ] at h
          simp only [Option.some.injEq] at h
          have hρM := tgt_lt_M_of_psi hm hz hzM'
          obtain ⟨h1, h2, -⟩ := ih true ρ u' (by simp only [↓reduceIte]; omega) hρF (fun _ => hρM) hρ
          split at h
          · rename_i hlt
            subst h
            exact ⟨by simp [selfVis, h1, le_leB (Or.inr (ltB_iff.mp hlt))], h2,
              fun _ => Or.inr (ltB_iff.mp hlt)⟩
          · subst h
            exact ⟨selfVis_self (Or.inr ⟨_, _, rfl⟩), hzM', fun _ => Or.inl rfl⟩
      | Xi j ζ =>
        rw [kNd_t_xi] at h
        have hζF := hz.xi.2.1
        simp only [Tm.size] at hn
        split at h
        · split at h
          · cases hζ : kNd m X false ζ with
            | none => rw [hζ] at h; cases h
            | some u' =>
              rw [hζ] at h
              simp only [Option.some.injEq] at h
              obtain ⟨h1, h2, -⟩ := ih false ζ u' (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
                hζF (fun e => by cases e) hζ
              split at h
              · rename_i hlt
                subst h
                exact ⟨by simp [selfVis, h1, le_leB (Or.inr (ltB_iff.mp hlt))], h2,
                  fun _ => Or.inr (ltB_iff.mp hlt)⟩
              · subst h
                exact ⟨selfVis_self (Or.inl ⟨_, _, rfl⟩), hzM', fun _ => Or.inl rfl⟩
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨selfVis_self (Or.inl ⟨_, _, rfl⟩), hzM', fun _ => Or.inl rfl⟩
        · cases h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hn
      cases z with
      | zero => rw [kNd_f_zero] at h; cases h
      | M j => rw [kNd_f_M] at h; cases h
      | plus a b =>
        rw [kNd_f_plus] at h
        obtain ⟨ha, hb, -, -⟩ := hz.plus
        simp only [Tm.size] at hn
        rcases maxOpt_cases h with h' | h'
        · obtain ⟨h1, h2, -⟩ := ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) ha
            (fun e => by cases e) h'
          exact ⟨by simp [selfVis, h1], h2, fun e => by cases e⟩
        · obtain ⟨h1, h2, -⟩ := ih false b u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hb
            (fun e => by cases e) h'
          exact ⟨by simp [selfVis, h1], h2, fun e => by cases e⟩
      | Om e =>
        rw [kNd_f_om] at h
        simp only [Tm.size] at hn
        obtain ⟨h1, h2, -⟩ := ih false e u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hz.om.1
          (fun e => by cases e) h
        exact ⟨by simp [selfVis, h1], h2, fun e => by cases e⟩
      | Xi j a =>
        rw [kNd_f_xi] at h
        split at h
        · rename_i hlt
          obtain ⟨h1, h2, -⟩ := ih true (.Xi j a) u (by simp only [↓reduceIte]; omega) hz
            (fun _ => ltB_iff.mp hlt) h
          exact ⟨h1, h2, fun e => by cases e⟩
        · rename_i hnlt
          simp only [Tm.size] at hn
          obtain ⟨h1, h2, -⟩ := ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
            hz.xi.2.1 (fun e => by cases e) h
          have huF := hz.xi.2.1.of_mem_subs (selfVis_mem h1)
          have hle : Le (.M m) (.Xi j a) := le_of_not_ltY hz hMF (fun h' => hnlt (ltB_iff.mpr h'))
          have hlt : Lt u (.Xi j a) := lt_of_lt_of_leY huF hMF hz h2 hle
          exact ⟨by simp [selfVis, h1, le_leB (Or.inr hlt)], h2, fun e => by cases e⟩
      | Psi p a =>
        rw [kNd_f_psi] at h
        split at h
        · rename_i hlt
          obtain ⟨h1, h2, -⟩ := ih true (.Psi p a) u (by simp only [↓reduceIte]; omega) hz
            (fun _ => ltB_iff.mp hlt) h
          exact ⟨h1, h2, fun e => by cases e⟩
        · rename_i hnlt
          simp only [Tm.size] at hn
          have hle : Le (.M m) (.Psi p a) := le_of_not_ltY hz hMF (fun h' => hnlt (ltB_iff.mpr h'))
          rcases maxOpt_cases h with h' | h'
          · obtain ⟨h1, h2, -⟩ := ih false p u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
              hz.psi.piF (fun e => by cases e) h'
            have huF := hz.psi.piF.of_mem_subs (selfVis_mem h1)
            have hlt : Lt u (.Psi p a) := lt_of_lt_of_leY huF hMF hz h2 hle
            exact ⟨by simp [selfVis, h1, le_leB (Or.inr hlt)], h2, fun e => by cases e⟩
          · obtain ⟨h1, h2, -⟩ := ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
              hz.psi.aF (fun e => by cases e) h'
            have huF := hz.psi.aF.of_mem_subs (selfVis_mem h1)
            have hlt : Lt u (.Psi p a) := lt_of_lt_of_leY huF hMF hz h2 hle
            exact ⟨by simp [selfVis, h1, le_leB (Or.inr hlt)], h2, fun e => by cases e⟩

theorem kNd_true_spec {m : Nat} {X z u : Tm} (hm : 1 ≤ m) (hz : WNF z) (hzM : Lt z (.M m))
    (h : kNd m X true z = some u) : WNF u ∧ selfVis u z = true ∧ Lt u (.M m) ∧ Le u z := by
  obtain ⟨h1, h2, h3⟩ := kNd_spec hm _ true z u (Nat.le_refl _) hz (fun _ => hzM) h
  exact ⟨hz.of_mem_subs (selfVis_mem h1), h1, h2, h3 rfl⟩

theorem kNd_false_spec {m : Nat} {X z u : Tm} (hm : 1 ≤ m) (hz : WNF z)
    (h : kNd m X false z = some u) : WNF u ∧ selfVis u z = true ∧ Lt u (.M m) := by
  obtain ⟨h1, h2, -⟩ := kNd_spec hm _ false z u (Nat.le_refl _) hz (fun e => by cases e) h
  exact ⟨hz.of_mem_subs (selfVis_mem h1), h1, h2⟩

/-- 引数の中の探索は、`M_m` についての前線の元の探索の最大のもの以上 -/
theorem kNd_front {m : Nat} {X : Tm} (hm : 1 ≤ m) : ∀ (ζ : Tm), WNF ζ → ∀ w, w ∈ fr (.M m) ζ →
    ∀ u', kNd m X true w = some u' → ∃ u, kNd m X false ζ = some u ∧ Le u' u
  | .zero, _, w, hw, _, _ => by rw [← frB_eq_fr] at hw; simp [frB] at hw
  | .M _, _, w, hw, _, _ => by rw [← frB_eq_fr] at hw; simp [frB] at hw
  | .plus a b, hz, w, hw, u', h => by
    obtain ⟨ha, hb, -, -⟩ := hz.plus
    rw [kNd_f_plus]
    rw [← frB_eq_fr] at hw
    simp only [frB, List.mem_append] at hw
    have hu'F : WNF u' := by
      rcases hw with hw | hw
      · rw [frB_eq_fr] at hw
        exact (kNd_true_spec hm (ha.of_mem_subs (fr_spec hw).1) (fr_spec hw).2 h).1
      · rw [frB_eq_fr] at hw
        exact (kNd_true_spec hm (hb.of_mem_subs (fr_spec hw).1) (fr_spec hw).2 h).1
    rcases hw with hw | hw
    · rw [frB_eq_fr] at hw
      obtain ⟨x, hx, hle⟩ := kNd_front hm a ha w hw u' h
      have hxF := (kNd_false_spec hm ha hx).1
      obtain ⟨y, hy, hle'⟩ := maxOpt_ge_l hx hxF (fun q hq => (kNd_false_spec hm hb hq).1)
      have hyF : WNF y := by
        rcases maxOpt_cases hy with h' | h'
        · exact (kNd_false_spec hm ha h').1
        · exact (kNd_false_spec hm hb h').1
      exact ⟨y, hy, le_transY hu'F hxF hyF hle hle'⟩
    · rw [frB_eq_fr] at hw
      obtain ⟨x, hx, hle⟩ := kNd_front hm b hb w hw u' h
      have hxF := (kNd_false_spec hm hb hx).1
      obtain ⟨y, hy, hle'⟩ := maxOpt_ge_r hx hxF (fun q hq => (kNd_false_spec hm ha hq).1)
      have hyF : WNF y := by
        rcases maxOpt_cases hy with h' | h'
        · exact (kNd_false_spec hm ha h').1
        · exact (kNd_false_spec hm hb h').1
      exact ⟨y, hy, le_transY hu'F hxF hyF hle hle'⟩
  | .Om e, hz, w, hw, u', h => by
    rw [kNd_f_om]
    rw [← frB_eq_fr] at hw
    simp only [frB] at hw
    rw [frB_eq_fr] at hw
    exact kNd_front hm e hz.om.1 w hw u' h
  | .Xi j a, hz, w, hw, u', h => by
    rw [kNd_f_xi]
    rw [← frB_eq_fr] at hw
    simp only [frB] at hw
    split at hw
    · rename_i hlt
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [hlt, ↓reduceIte]
      exact ⟨u', h, Or.inl rfl⟩
    · rename_i hnlt
      simp only [hnlt]
      rw [frB_eq_fr] at hw
      exact kNd_front hm a hz.xi.2.1 w hw u' h
  | .Psi p a, hz, w, hw, u', h => by
    rw [kNd_f_psi]
    rw [← frB_eq_fr] at hw
    simp only [frB] at hw
    split at hw
    · rename_i hlt
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [hlt, ↓reduceIte]
      exact ⟨u', h, Or.inl rfl⟩
    · rename_i hnlt
      simp only [hnlt]
      have hpF := hz.psi.piF
      have haF := hz.psi.aF
      simp only [List.mem_append] at hw
      have hu'F : WNF u' := by
        rcases hw with hw | hw
        · rw [frB_eq_fr] at hw
          exact (kNd_true_spec hm (hpF.of_mem_subs (fr_spec hw).1) (fr_spec hw).2 h).1
        · rw [frB_eq_fr] at hw
          exact (kNd_true_spec hm (haF.of_mem_subs (fr_spec hw).1) (fr_spec hw).2 h).1
      rcases hw with hw | hw
      · rw [frB_eq_fr] at hw
        obtain ⟨x, hx, hle⟩ := kNd_front hm p hpF w hw u' h
        have hxF := (kNd_false_spec hm hpF hx).1
        obtain ⟨y, hy, hle'⟩ := maxOpt_ge_l hx hxF (fun q hq => (kNd_false_spec hm haF hq).1)
        have hyF : WNF y := by
          rcases maxOpt_cases hy with h' | h'
          · exact (kNd_false_spec hm hpF h').1
          · exact (kNd_false_spec hm haF h').1
        exact ⟨y, hy, le_transY hu'F hxF hyF hle hle'⟩
      · rw [frB_eq_fr] at hw
        obtain ⟨x, hx, hle⟩ := kNd_front hm a haF w hw u' h
        have hxF := (kNd_false_spec hm haF hx).1
        obtain ⟨y, hy, hle'⟩ := maxOpt_ge_r hx hxF (fun q hq => (kNd_false_spec hm hpF hq).1)
        have hyF : WNF y := by
          rcases maxOpt_cases hy with h' | h'
          · exact (kNd_false_spec hm hpF h').1
          · exact (kNd_false_spec hm haF h').1
        exact ⟨y, hy, le_transY hu'F hxF hyF hle hle'⟩

/-! ### 障害が `s` 以下の項は塔の下 -/

/-- `z` の障害は `s` 以下 -/
def KD (m : Nat) (X s z : Tm) : Prop := ∀ u, kNd m X true z = some u → Le u s

/-- 障害が塔の 1 段目より小さい `s` 以下の項は塔の下 -/
theorem kTop_hull {m : Nat} {Y R : Tm} {pre : List Tm} (hY : WNF Y)
    (hsY : summands Y = pre ++ [R]) (hRi : BigInv R (.M m))
    {γ : Nat → Tm} (hγF : ∀ k, WNF (γ k)) (hγM : ∀ k, Lt (γ k) (.M m))
    (hγm : ∀ k, Lt (γ k) (γ (k + 1)))
    (hγS : ∀ k, γ (k + 1) = .Xi m (oadd (ofSummands pre) (fundBig R (γ k))))
    {s : Tm} (hsF : WNF s) (hs : Lt s (γ 1)) :
    ∀ z, WNF z → Lt z (.M m) → KD m Y s z → ∃ k, Lt z (γ k) := by
  have hm : 1 ≤ m := by have h := hγF 1; rw [hγS 0] at h; exact h.xi.1
  have hMF := WNF.M' hm
  have H := xi_tower_hull hY hsY hRi hγF hγM hγm hγS (fun z => Lt z (.M m) ∧ KD m Y s z)
    (fun z h => h.1) (fun z hz ⟨hzM, hKD⟩ => by
      have hsmall : Le z s → ∃ k, Lt z (γ k) := fun h =>
        ⟨1, lt_of_le_of_ltY hz hsF (hγF 1) h hs⟩
      cases z with
      | zero =>
        exact Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun _ _ e => (nomatch e),
          fun _ e => (nomatch e)⟩
      | M j =>
        exact Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun _ _ e => (nomatch e),
          fun _ e => (nomatch e)⟩
      | plus a b =>
        obtain ⟨ha, hb, -, -⟩ := hz.plus
        refine Or.inr ⟨fun a' b' e => ?_, fun _ e => (nomatch e), fun _ _ e => (nomatch e),
          fun _ e => (nomatch e)⟩
        cases e
        refine ⟨lt_transY ha hz hMF (lt_plus_leftY hz) hzM, fun u hu => ?_⟩
        have huF := (kNd_true_spec hm ha (lt_transY ha hz hMF (lt_plus_leftY hz) hzM) hu).1
        obtain ⟨x, hx, hle⟩ := maxOpt_ge_l hu huF (fun q hq =>
          (kNd_true_spec hm hb (lt_transY hb hz hMF (lt_plus_rightY hz) hzM) hq).1)
        have hxF : WNF x := (kNd_true_spec hm hz hzM (by rw [kNd_t_plus]; exact hx)).1
        exact le_transY huF hxF hsF hle (hKD x (by rw [kNd_t_plus]; exact hx))
      | Om e =>
        refine Or.inr ⟨fun _ _ e' => (nomatch e'), fun e' h' => ?_, fun _ _ e' => (nomatch e'),
          fun _ e' => (nomatch e')⟩
        cases h'
        exact ⟨lt_transY hz.om.1 hz hMF (lt_om_selfY hz) hzM, fun u hu => hKD u (by rw [kNd_t_om]; exact hu)⟩
      | Psi ρ a =>
        have hρM := tgt_lt_M_of_psi hm hz hzM
        cases hρ : kNd m Y true ρ with
        | none =>
          refine Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun ρ' a' e => ?_,
            fun _ e => (nomatch e)⟩
          cases e
          exact ⟨hρM, fun u hu => by rw [hρ] at hu; cases hu⟩
        | some u' =>
          by_cases hlt : ltB u' (.Psi ρ a) = true
          · refine Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun ρ' a' e => ?_,
              fun _ e => (nomatch e)⟩
            cases e
            refine ⟨hρM, fun u hu => ?_⟩
            rw [hρ] at hu
            cases hu
            exact hKD u' (by rw [kNd_t_psi, hρ]; simp [hlt])
          · exact Or.inl (hsmall (hKD (.Psi ρ a) (by rw [kNd_t_psi, hρ]; simp [hlt])))
      | Xi j ζ =>
        by_cases hj : j = m
        · subst hj
          by_cases hζ : ltB ζ Y = true
          · cases hf : kNd j Y false ζ with
            | none =>
              refine Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun _ _ e => (nomatch e),
                fun ζ' e => ?_⟩
              cases e
              refine ⟨ltB_iff.mp hζ, fun w hw => ⟨(fr_spec hw).2, fun u hu => ?_⟩⟩
              obtain ⟨u2, hu2, -⟩ := kNd_front hm ζ hz.xi.2.1 w hw u hu
              rw [hf] at hu2
              cases hu2
            | some u' =>
              by_cases hlt : ltB u' (.Xi j ζ) = true
              · refine Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e),
                  fun _ _ e => (nomatch e), fun ζ' e => ?_⟩
                cases e
                refine ⟨ltB_iff.mp hζ, fun w hw => ⟨(fr_spec hw).2, fun u hu => ?_⟩⟩
                obtain ⟨u2, hu2, hle⟩ := kNd_front hm ζ hz.xi.2.1 w hw u hu
                rw [hf] at hu2
                cases hu2
                have hwF := hz.xi.2.1.of_mem_subs (fr_spec hw).1
                have huF := (kNd_true_spec hm hwF (fr_spec hw).2 hu).1
                have hu'F := (kNd_false_spec hm hz.xi.2.1 hf).1
                exact le_transY huF hu'F hsF hle (hKD u' (by rw [kNd_t_xi]; simp [hζ, hf, hlt]))
              · exact Or.inl (hsmall (hKD (.Xi j ζ) (by rw [kNd_t_xi]; simp [hζ, hf, hlt])))
          · exact Or.inl (hsmall (hKD (.Xi j ζ) (by rw [kNd_t_xi]; simp [hζ])))
        · refine Or.inr ⟨fun _ _ e => (nomatch e), fun _ e => (nomatch e), fun _ _ e => (nomatch e),
            fun ζ' e => ?_⟩
          cases e
          exact absurd rfl hj)
  exact fun z hz hzM hKD => H z hz ⟨hzM, hKD⟩

/-! ### 始点 -/

theorem kNeed_spec {m : Nat} {τ X s : Tm} (h : kNeed m τ X = some s) :
    ∃ e, e ∈ fr τ τ ∧ kNd m X true e = some s := by
  unfold kNeed at h
  obtain ⟨e, he, hf⟩ := foldr_maxOpt_spec h
  rw [frB_eq_fr] at he
  exact ⟨e, he, hf⟩

theorem kNeed_ge {m : Nat} {τ X e u : Tm} (hm : 1 ≤ m) (hτ : WNF τ) (hτM : Lt τ (.M m))
    (he : e ∈ fr τ τ) (h : kNd m X true e = some u) : ∃ s, kNeed m τ X = some s ∧ Le u s := by
  have hMF := WNF.M' hm
  have hwf : ∀ e', e' ∈ frB τ τ → ∀ q, kNd m X true e' = some q → WNF q := fun e' he' q hq => by
    rw [frB_eq_fr] at he'
    have he'F := hτ.of_mem_subs (fr_spec he').1
    exact (kNd_true_spec hm he'F (lt_transY he'F hτ hMF (fr_spec he').2 hτM) hq).1
  obtain ⟨x, hx, hl⟩ := foldr_maxOpt_ge (f := kNd m X true) hwf (by rw [frB_eq_fr]; exact he) h
  exact ⟨x, hx, hl⟩

/-- 目標の前線の元の障害は、`kNeed` の値以下 -/
theorem kNeed_KD {m : Nat} {τ X s e : Tm} (hm : 1 ≤ m) (hτ : WNF τ) (hτM : Lt τ (.M m))
    (hs : kNeed m τ X = some s) (he : e ∈ fr τ τ) : KD m X s e := by
  intro u hu
  obtain ⟨s', hs', hle⟩ := kNeed_ge hm hτ hτM he hu
  rw [hs] at hs'
  cases hs'
  exact hle

theorem kNeed_none {m : Nat} {τ X e : Tm} (hm : 1 ≤ m) (hτ : WNF τ) (hτM : Lt τ (.M m))
    (hs : kNeed m τ X = none) (he : e ∈ fr τ τ) : ∀ s, KD m X s e := by
  intro s u hu
  obtain ⟨s', hs', -⟩ := kNeed_ge hm hτ hτM he hu
  rw [hs] at hs'
  cases hs'

/-- 始点の場合分け -/
theorem kTop_cases (τ : Tm) (m : Nat) (pre : List Tm) (R : Tm) (r : SeqD) :
    (kNeed m τ (oadd (ofSummands pre) R) = none ∧ kTop τ m pre R r = .zero) ∨
      ∃ s, kNeed m τ (oadd (ofSummands pre) R) = some s ∧
        ((kTop τ m pre R r = .zero ∧ Lt s (.Xi m (oadd (ofSummands pre) (r.big .zero)))) ∨
          kTop τ m pre R r = s) := by
  unfold kTop
  cases h : kNeed m τ (oadd (ofSummands pre) R) with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some s =>
    refine Or.inr ⟨s, rfl, ?_⟩
    dsimp only
    split
    · rename_i hlt
      exact Or.inl ⟨rfl, ltB_iff.mp hlt⟩
    · exact Or.inr rfl

/-- 始点の性質：標準形、`M_m` 未満、目標の前線の元が `C(g, d)` に入れば始点も入る -/
theorem kTop_spec {τ : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} (hm : 1 ≤ m) (hτ : WNF τ)
    (hτM : Lt τ (.M m)) :
    WNF (kTop τ m pre R r) ∧ Lt (kTop τ m pre R r) (.M m) ∧
      ∀ g d, Cut d → (∀ e, e ∈ fr τ τ → inC e g d = true) → inC (kTop τ m pre R r) g d = true := by
  have hMF := WNF.M' hm
  have h0 : WNF (Tm.zero) ∧ Lt .zero (.M m) ∧
      ∀ g d, Cut d → (∀ e, e ∈ fr τ τ → inC e g d = true) → inC .zero g d = true :=
    ⟨WNF.zero, zero_lt (by intro e; cases e), fun _ _ _ _ => inC_zero _ _⟩
  rcases kTop_cases τ m pre R r with ⟨-, e⟩ | ⟨s, hs, ⟨e, -⟩ | e⟩
  · rw [e]; exact h0
  · rw [e]; exact h0
  · rw [e]
    obtain ⟨e', he', hf⟩ := kNeed_spec hs
    have he'F := hτ.of_mem_subs (fr_spec he').1
    obtain ⟨hsF, h1, h2, -⟩ := kNd_true_spec hm he'F (lt_transY he'F hτ hMF (fr_spec he').2 hτM) hf
    exact ⟨hsF, h2, fun g d hd hC => inC_of_selfVis hsF hd he'F h1 (hC e' he')⟩

end MahloOCF.FS
