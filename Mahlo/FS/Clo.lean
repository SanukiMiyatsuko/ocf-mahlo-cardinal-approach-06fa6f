import Mahlo.FS.Base

/-! 共終性の道具。

* 閉じた点 `Cl σ β`：`σ` 未満で `σ` についての前線が `β` 未満の項は `β` 未満。`σ` への崩壊 `Ψ_σ(A)`、
  `M_m` については `Ξ_m(A)` が閉じた点（`Cl.of_psi`・`Cl.of_xi`）。
* 成分の前線 `parF x`（和の加数、`Ω_e` の `e`、`Ξ_j(b)` の `b` の `M_j` についての前線、`Ψ_ρ(a)` の `a`・`ρ` の
  `ρ` についての前線）は `x` 未満の真の部分項。
* 崩壊への移し替えの一歩（`psi_step`）：`x < Ψ_π(X)` で `x` の成分の前線が `Ψ_π(A)` 未満なら、`x` が
  `Ψ_π(a)` の形で `a ≥ A` のときを除いて `x < Ψ_π(A)`。
* 共終性の帰納法（`cof_nat`）：成分が列の項の下に入れば `x` も入る、を示せば共終。 -/

namespace MahloOCF.FS

open Tm

/-! ### 前線と加数 -/

theorem mem_fr_iff {R : Tm} : ∀ {x f : Tm}, f ∈ fr R x ↔ ∃ u, u ∈ summands x ∧ f ∈ fr R u
  | .zero, f => by simp [fr, summands]
  | .plus a b, f => by
    rw [fr, List.mem_append, mem_fr_iff (x := b)]
    constructor
    · rintro (h | ⟨u, hu, hf⟩)
      · exact ⟨a, by simp [summands], h⟩
      · exact ⟨u, by simp [summands, hu], hf⟩
    · rintro ⟨u, hu, hf⟩
      simp only [summands, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact Or.inl hf
      · exact Or.inr ⟨u, hu, hf⟩
  | .M _, f | .Om _, f | .Xi _ _, f | .Psi _ _, f => by
    simp [summands]

/-- `y` の加数が全て `x` の加数なら、`y` の前線は `x` の前線 -/
theorem fr_sub_of_summands {R x y : Tm} (h : ∀ u, u ∈ summands y → u ∈ summands x) {f : Tm}
    (hf : f ∈ fr R y) : f ∈ fr R x := by
  obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
  exact mem_fr_iff.mpr ⟨u, h u hu, hfu⟩

/-- 前線による `C` への所属：`x ∈ C(g0, R)`、`d ≤ R`、`g0 ≤ g` で、前線（`R` について）が `d` 未満なら
    `x ∈ C(g, d)` -/
theorem inC_of_fr_lt {x R g0 g d : Tm} (hx : WNF x) (hR : WNF R) (hd : WNF d) (hg0 : WNF g0)
    (hg : WNF g) (h0 : inC x g0 R = true) (hdR : Le d R) (hgg : Le g0 g)
    (hf : ∀ w, w ∈ fr R x → Lt w d) : inC x g d = true := by
  refine (inC_fr x h0 (fun w hw hwR hwd => hwR ?_) (fun v hv hvg => ?_)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (hf w hw))
  · exact lt_of_lt_of_leY (hx.of_mem_subs hw) hd hR hwd hdR
  · exact lt_of_lt_of_leY (hx.of_mem_subs hv) hg0 hg hvg hgg

theorem _root_.MahloOCF.IsRegY.principal {σ : Tm} (h : IsRegY σ) : isPrincipal σ = true := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩ <;> rfl

theorem wnf_base {σ : Tm} (hσ : WNF σ) (hreg : IsRegY σ) : WNF (base σ) := by
  rcases hreg with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact wnf_base_om hσ (Or.inl rfl)
  · exact wnf_base_om hσ (Or.inr hs)
  · exact wnf_kTerm _
  · exact wnf_base_xi hσ

theorem base_lt {σ : Tm} (hσ : WNF σ) (hreg : IsRegY σ) : Lt (base σ) σ := by
  rcases hreg with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact base_om_lt _
  · exact base_om_lt _
  · exact kTerm_lt_M hσ.M
  · exact psi_xi_lt_xi n p _

/-! ### `σ` 未満の極大の部分項 -/

/-- `x` の `σ` 未満の極大の部分項（`σ` 以上の部分項だけを通って現れるもの） -/
def lfr (σ : Tm) : Tm → List Tm
  | .zero => if Lt .zero σ then [.zero] else []
  | .M n => if Lt (.M n) σ then [.M n] else []
  | .plus a b => if Lt (.plus a b) σ then [.plus a b] else lfr σ a ++ lfr σ b
  | .Om a => if Lt (.Om a) σ then [.Om a] else lfr σ a
  | .Xi m a => if Lt (.Xi m a) σ then [.Xi m a] else lfr σ a
  | .Psi p a => if Lt (.Psi p a) σ then [.Psi p a] else lfr σ p ++ lfr σ a

theorem lfr_of_lt {σ x : Tm} (h : Lt x σ) : lfr σ x = [x] := by
  cases x <;> simp [lfr, h]

theorem lfr_spec {σ : Tm} : ∀ {x f : Tm}, f ∈ lfr σ x → f ∈ subs x ∧ Lt f σ
  | .zero, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · cases h
  | .M n, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · cases h
  | .plus a b, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · rcases List.mem_append.mp h with h | h
      · exact ⟨subs_plus_l (lfr_spec h).1, (lfr_spec h).2⟩
      · exact ⟨subs_plus_r (lfr_spec h).1, (lfr_spec h).2⟩
  | .Om a, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · exact ⟨subs_om (lfr_spec h).1, (lfr_spec h).2⟩
  | .Xi m a, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · exact ⟨subs_xi (lfr_spec h).1, (lfr_spec h).2⟩
  | .Psi p a, f, h => by
    simp only [lfr] at h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨self_mem_subs _, by assumption⟩
    · rcases List.mem_append.mp h with h | h
      · exact ⟨subs_psi_p (lfr_spec h).1, (lfr_spec h).2⟩
      · exact ⟨subs_psi_a (lfr_spec h).1, (lfr_spec h).2⟩

/-- `lfr` の元は項以下 -/
theorem lfr_le {σ : Tm} (hσ : WNF σ) {x f : Tm} (hx : WNF x) (h : f ∈ lfr σ x) : Le f x := by
  by_cases hxσ : Lt x σ
  · rw [lfr_of_lt hxσ, List.mem_singleton] at h; rw [h]; exact Or.inl rfl
  · obtain ⟨hf, hfσ⟩ := lfr_spec h
    exact Or.inr (lt_of_lt_of_leY (hx.of_mem_subs hf) hσ hx hfσ (le_of_not_ltY hx hσ hxσ))

/-- `σ` 以上の項の `lfr` は成分の `lfr` -/
theorem mem_lfr_plus {σ a b f : Tm} (h : ¬ Lt (.plus a b) σ) :
    f ∈ lfr σ (.plus a b) ↔ f ∈ lfr σ a ∨ f ∈ lfr σ b := by
  simp only [lfr, h, ↓reduceIte, List.mem_append]

theorem mem_lfr_om {σ a f : Tm} (h : ¬ Lt (.Om a) σ) : f ∈ lfr σ (.Om a) ↔ f ∈ lfr σ a := by
  simp only [lfr, h, ↓reduceIte]

theorem mem_lfr_xi {σ a f : Tm} {m : Nat} (h : ¬ Lt (.Xi m a) σ) :
    f ∈ lfr σ (.Xi m a) ↔ f ∈ lfr σ a := by
  simp only [lfr, h, ↓reduceIte]

theorem mem_lfr_psi {σ p a f : Tm} (h : ¬ Lt (.Psi p a) σ) :
    f ∈ lfr σ (.Psi p a) ↔ f ∈ lfr σ p ∨ f ∈ lfr σ a := by
  simp only [lfr, h, ↓reduceIte, List.mem_append]

/-- `lfr` の元の前線（`σ` について、節点の）は全体の前線 -/
theorem fr_of_lfr {σ : Tm} : ∀ {x g f : Tm}, WNF x → g ∈ lfr σ x → f ∈ fr σ g →
    f ∈ fr σ x := by
  intro x
  induction x using size_induction with
  | h x ih =>
  intro g f hx hg hf
  by_cases hxσ : Lt x σ
  · rw [lfr_of_lt hxσ, List.mem_singleton] at hg; subst hg; exact hf
  cases x with
  | zero | M _ =>
    simp only [lfr, hxσ, ↓reduceIte] at hg; cases hg
  | plus a b =>
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rcases (mem_lfr_plus hxσ).mp hg with hg | hg
    · exact fr_mem_plus_l (ih a (by simp only [Tm.size]; omega) ha hg hf)
    · exact fr_mem_plus_r (ih b (by simp only [Tm.size]; omega) hb hg hf)
  | Om a =>
    exact fr_mem_om (ih a (by simp only [Tm.size]; omega) hx.om.1 ((mem_lfr_om hxσ).mp hg) hf)
  | Xi m a =>
    exact fr_mem_xi hxσ (ih a (by simp only [Tm.size]; omega) hx.xi.2.1 ((mem_lfr_xi hxσ).mp hg) hf)
  | Psi p a =>
    have hP := hx.psi
    rcases (mem_lfr_psi hxσ).mp hg with hg | hg
    · exact fr_mem_psi_p hxσ (ih p (by simp only [Tm.size]; omega) hP.piF hg hf)
    · exact fr_mem_psi_a hxσ (ih a (by simp only [Tm.size]; omega) hP.aF hg hf)

/-- 前線の元の `lfr` は全体の `lfr` の元以下：`w` が `b` の `R` についての前線の元で `σ ≤ R` -/
theorem lfr_of_fr {R σ : Tm} (hR : WNF R) (hσ : WNF σ) :
    ∀ {b w f : Tm}, WNF b → w ∈ fr R b → f ∈ lfr σ w → ∃ g, g ∈ lfr σ b ∧ Le f g := by
  intro b
  induction b using size_induction with
  | h b ih =>
  intro w f hb hw hf
  have hwF := hb.of_mem_subs (fr_spec hw).1
  have hfF := hwF.of_mem_subs (lfr_spec hf).1
  by_cases hbσ : Lt b σ
  · refine ⟨b, by rw [lfr_of_lt hbσ]; exact List.mem_singleton.mpr rfl, ?_⟩
    exact le_transY hfF hwF hb (lfr_le hσ hwF hf) (fr_leY hR hb hw)
  cases b with
  | zero | M _ => simp [fr] at hw
  | plus a c =>
    obtain ⟨ha, hc, -, -⟩ := hb.plus
    rw [fr, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨g, hg, hfg⟩ := ih a (by simp only [Tm.size]; omega) ha hw hf
      exact ⟨g, (mem_lfr_plus hbσ).mpr (Or.inl hg), hfg⟩
    · obtain ⟨g, hg, hfg⟩ := ih c (by simp only [Tm.size]; omega) hc hw hf
      exact ⟨g, (mem_lfr_plus hbσ).mpr (Or.inr hg), hfg⟩
  | Om a =>
    rw [fr] at hw
    obtain ⟨g, hg, hfg⟩ := ih a (by simp only [Tm.size]; omega) hb.om.1 hw hf
    exact ⟨g, (mem_lfr_om hbσ).mpr hg, hfg⟩
  | Xi m a =>
    rw [fr] at hw
    by_cases hlt : Lt (.Xi m a) R
    · simp only [hlt, ↓reduceIte, List.mem_singleton] at hw
      subst hw
      exact ⟨f, hf, Or.inl rfl⟩
    · simp only [hlt, ↓reduceIte] at hw
      obtain ⟨g, hg, hfg⟩ := ih a (by simp only [Tm.size]; omega) hb.xi.2.1 hw hf
      exact ⟨g, (mem_lfr_xi hbσ).mpr hg, hfg⟩
  | Psi p a =>
    have hP := hb.psi
    rw [fr] at hw
    by_cases hlt : Lt (.Psi p a) R
    · simp only [hlt, ↓reduceIte, List.mem_singleton] at hw
      subst hw
      exact ⟨f, hf, Or.inl rfl⟩
    · simp only [hlt, ↓reduceIte, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨g, hg, hfg⟩ := ih p (by simp only [Tm.size]; omega) hP.piF hw hf
        exact ⟨g, (mem_lfr_psi hbσ).mpr (Or.inl hg), hfg⟩
      · obtain ⟨g, hg, hfg⟩ := ih a (by simp only [Tm.size]; omega) hP.aF hw hf
        exact ⟨g, (mem_lfr_psi hbσ).mpr (Or.inr hg), hfg⟩

/-! ### 閉じた点 -/

/-- `β` は `σ` の中で閉じた点：`σ` 未満で `σ` についての前線が `β` 未満の項は `β` 未満 -/
def Cl (σ β : Tm) : Prop := ∀ x, WNF x → Lt x σ → (∀ f, f ∈ fr σ x → Lt f β) → Lt x β

theorem Cl.pos {σ β : Tm} (h : Cl σ β) (hσ : Lt .zero σ) : Lt .zero β :=
  h .zero WNF.zero hσ (fun f hf => by simp [fr] at hf)

/-- `σ` への崩壊は `σ` の中で閉じた点 -/
theorem Cl.of_psi {σ A : Tm} (hβ : WNF (.Psi σ A)) : Cl σ (.Psi σ A) := by
  have hP := hβ.psi
  intro x hx hxσ hf
  exact coll_psiY hβ hx (inC_of_fr_lt hx hP.piF hβ hP.aF hP.aF (inC_of_ltY _ hx hP.piF hxσ)
    (Or.inr (lt_psi_targetY hβ)) (Or.inl rfl) hf) hxσ

/-- `Ξ_m(A)` は `M_m` の中で閉じた点 -/
theorem Cl.of_xi {m : Nat} {A : Tm} (hβ : WNF (.Xi m A)) : Cl (.M m) (.Xi m A) := by
  obtain ⟨hm, hAF, -, -⟩ := hβ.xi
  have hMF := WNF.M' hm
  have hβM : Lt (.Xi m A) (.M m) := lt_of_lev_lt' (by simp only [lev]; omega)
  intro x hx hxσ hf
  exact coll_xi0 hβ x hx (inC_of_fr_lt hx hMF hβ hAF hAF (inC_of_ltY _ hx hMF hxσ) (Or.inr hβM)
    (Or.inl rfl) hf) hxσ

/-! ### 成分の前線 -/

/-- `x` の成分の前線 -/
def parF : Tm → List Tm
  | .plus a b => [a, b]
  | .Om e => [e]
  | .Xi j b => fr (.M j) b
  | .Psi ρ a => fr ρ a ++ fr ρ ρ
  | _ => []

/-- 帰納法で使う成分（崩壊は崩壊先も） -/
def parL : Tm → List Tm
  | .Psi ρ a => ρ :: (fr ρ a ++ fr ρ ρ)
  | x => parF x

theorem parF_sub_parL {x w : Tm} (h : w ∈ parF x) : w ∈ parL x := by
  cases x with
  | Psi ρ a => exact List.mem_cons_of_mem _ h
  | _ => exact h

theorem parF_lt : ∀ {x w : Tm}, WNF x → w ∈ parF x → Lt w x
  | .zero, _, _, h | .M _, _, _, h => by simp [parF] at h
  | .plus a b, w, hx, h => by
    simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact lt_plus_leftY hx
    · exact lt_plus_rightY hx
  | .Om e, w, hx, h => by
    simp only [parF, List.mem_singleton] at h
    rw [h]
    exact lt_om_selfY hx
  | .Xi j b, w, hx, h => k2xY hx w h
  | .Psi ρ a, w, hx, h => by
    simp only [parF, List.mem_append] at h
    rcases h with h | h
    · exact k2Y hx w h
    · exact k2tY hx w h

theorem parL_sub : ∀ {x w : Tm}, w ∈ parL x → w ∈ subs x ∧ w.size < x.size
  | .zero, _, h | .M _, _, h => by simp [parL, parF] at h
  | .plus a b, w, h => by
    simp only [parL, parF, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨subs_plus_l (self_mem_subs _), by simp only [Tm.size]; omega⟩
    · exact ⟨subs_plus_r (self_mem_subs _), by simp only [Tm.size]; omega⟩
  | .Om e, w, h => by
    simp only [parL, parF, List.mem_singleton] at h
    rw [h]
    exact ⟨subs_om (self_mem_subs _), by simp only [Tm.size]; omega⟩
  | .Xi j b, w, h => by
    have h1 := (fr_spec (show w ∈ fr (.M j) b from h)).1
    have h2 := size_le_of_mem_subs h1
    exact ⟨subs_xi h1, by simp only [Tm.size]; omega⟩
  | .Psi ρ a, w, h => by
    simp only [parL, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact ⟨subs_psi_p (self_mem_subs _), by simp only [Tm.size]; omega⟩
    · have h1 := (fr_spec h).1
      have h2 := size_le_of_mem_subs h1
      exact ⟨subs_psi_a h1, by simp only [Tm.size]; omega⟩
    · have h1 := (fr_spec h).1
      have h2 := size_le_of_mem_subs h1
      exact ⟨subs_psi_p h1, by simp only [Tm.size]; omega⟩

theorem parF_mem_subs {x w : Tm} (h : w ∈ parF x) : w ∈ subs x := (parL_sub (parF_sub_parL h)).1

/-- `x ≥ σ` なら、成分の前線の `lfr` は `x` の `lfr` の元以下 -/
theorem lfr_of_parF {σ x w f : Tm} (hσ : WNF σ) (hx : WNF x) (hxσ : ¬ Lt x σ) (hw : w ∈ parF x)
    (hf : f ∈ lfr σ w) : ∃ g, g ∈ lfr σ x ∧ Le f g := by
  cases x with
  | zero | M _ => simp [parF] at hw
  | plus a b =>
    simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨f, (mem_lfr_plus hxσ).mpr (Or.inl hf), Or.inl rfl⟩
    · exact ⟨f, (mem_lfr_plus hxσ).mpr (Or.inr hf), Or.inl rfl⟩
  | Om e =>
    simp only [parF, List.mem_singleton] at hw
    subst hw
    exact ⟨f, (mem_lfr_om hxσ).mpr hf, Or.inl rfl⟩
  | Xi j b =>
    obtain ⟨hj, hbF, -, -⟩ := hx.xi
    have hMF := WNF.M' hj
    have hxM : Lt (.Xi j b) (.M j) := lt_of_lev_lt' (by simp only [lev]; omega)
    have hσM : Le σ (.M j) :=
      Or.inr (lt_of_le_of_ltY hσ hx hMF (le_of_not_ltY hx hσ hxσ) hxM)
    obtain ⟨g, hg, hfg⟩ := lfr_of_fr hMF hσ hbF hw hf
    exact ⟨g, (mem_lfr_xi hxσ).mpr hg, hfg⟩
  | Psi ρ a =>
    have hP := hx.psi
    have hσρ : Le σ ρ :=
      Or.inr (lt_of_le_of_ltY hσ hx hP.piF (le_of_not_ltY hx hσ hxσ) (lt_psi_targetY hx))
    simp only [parF, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨g, hg, hfg⟩ := lfr_of_fr hP.piF hσ hP.aF hw hf
      exact ⟨g, (mem_lfr_psi hxσ).mpr (Or.inr hg), hfg⟩
    · obtain ⟨g, hg, hfg⟩ := lfr_of_fr hP.piF hσ hP.piF hw hf
      exact ⟨g, (mem_lfr_psi hxσ).mpr (Or.inl hg), hfg⟩

/-! ### 崩壊への移し替えの一歩 -/

/-- `x < Ψ_π(X)` で、`x` の成分の前線が `Ψ_π(A)` 未満、`x = Ψ_ρ(a)` なら `ρ < Ψ_π(X)` のとき
    `ρ < Ψ_π(A)`、`x = Ψ_π(a)` なら `a < A`、のとき `x < Ψ_π(A)`（`Ψ_π(A)` は標準形） -/
theorem psi_step {π X A x : Tm} (ht : WNF (.Psi π X)) (hy : WNF (.Psi π A)) (hx : WNF x)
    (hxt : Lt x (.Psi π X)) (hF : ∀ w, w ∈ parF x → Lt w (.Psi π A))
    (hk : ∀ ρ a, x = .Psi ρ a → Lt ρ (.Psi π X) → Lt ρ (.Psi π A))
    (harg : ∀ a, x = .Psi π a → Lt a A) : Lt x (.Psi π A) := by
  have hP := ht.psi
  have hπ := hP.piF
  have hT := hP.tgt
  have hlev : lev x ≤ lev π := by have := lev_le_of_lt_gen hxt; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  have hm1 : 1 ≤ lev π := lev_posY hπ hT.ne_zero
  have hyM : Lt (.Psi π A) (.M (lev π)) := lt_of_lev_lt' (by simp only [lev]; omega)
  cases x with
  | zero => exact zero_lt (by intro e; cases e)
  | M k => exact M_lt_psi (by simp only [lev] at hl; omega)
  | plus a b => exact (lt_plus_prin_iffY hx rfl).mpr (hF a (by simp [parF]))
  | Om e =>
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_psiOmG.mp hxt)
    · exact lt_om_psiOmG.mpr (lt_om_psiOmG.mp hxt)
    · exact (lt_om_OF' (Or.inr ⟨n, p, A, rfl⟩) (by simp only [lev]; exact hπ.xi.1)).mpr
        (hF e (by simp [parF]))
  | Xi j b =>
    simp only [lev] at hl
    obtain ⟨hj, hbF, -, hbC⟩ := hx.xi
    obtain ⟨hgt, -⟩ := (lt_xi_psi_iff (π := π) (γ := X) (f := b) (n := j) hl.symm).mp hxt
    refine (lt_xi_psi_iff (π := π) (γ := A) (f := b) (n := j) hl.symm).mpr ⟨hgt, ?_⟩
    refine (baseOf_xi_iff j b _).mpr ⟨kTerm_lt_psi hj hl.symm, ?_⟩
    rw [← hl] at hyM
    exact inC_of_fr_lt hbF (WNF.M' hj) hy hbF hbF hbC (Or.inr hyM) (Or.inl rfl)
      (fun w hw => hF w hw)
  | Psi ρ a =>
    have hQ := hx.psi
    have hρF := hQ.piF
    have hlρ : lev ρ = lev π := by simpa [lev] using hl
    rcases triY hρF hπ with hρπ | rfl | hπρ
    · -- `ρ < π`
      have hne : ρ ≠ π := fun e => Lt.ne hρπ e
      have hnlt := Lt.asymmY hρF hπ hρπ
      rcases triY hρF ht with hρt | e | htρ
      · exact lt_transY hx hρF hy (lt_psi_targetY hx) (hk ρ a rfl hρt)
      · exfalso; rcases hQ.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> cases e
      · rcases triY hρF hy with hρy | e | hyρ
        · exact lt_transY hx hρF hy (lt_psi_targetY hx) hρy
        · exfalso; rcases hQ.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> cases e
        · refine (lt_psi_psi_ltT (β := a) (γ := A) hlρ hne hnlt).mpr ?_
          rcases hQ.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨m, e, rfl⟩
          · exact (baseOf_om_zero _).mpr (by intro e; cases e)
          · -- `Ω_c` は `t` と `π` の間に入らない
            exfalso
            rcases hT with rfl | ⟨c', rfl, hs'⟩ | ⟨n, p, rfl⟩
            · exact not_lt_zero _ (lt_om_iffG.mp hρπ)
            · have h1 : Le c' c := (lt_psiOm_omY ht hρF.om.1).mp htρ
              exact not_lt_of_leY hπ.om.1 hρF.om.1 h1 (lt_om_iffG.mp hρπ)
            · have hOF : IsOF (Tm.Psi (.Xi n p) X) := Or.inr ⟨n, p, X, rfl⟩
              have h1 : Lt (Tm.Psi (.Xi n p) X) c := (lt_OF_omY hOF ht hρF.om.1).mp htρ
              have h2 : Lt (Tm.Psi (.Xi n p) X) (.Psi (.Om c) a) :=
                (lt_OF_psiOmY hOF ht hx).mpr h1
              exact Lt.asymmY hx ht hxt h2
          · have hm := hρF.xi.1
            have hlm : lev π = m := by simp only [lev] at hlρ; exact hlρ.symm
            refine (baseOf_xi_iff m e _).mpr ⟨kTerm_lt_psi hm hlm, ?_⟩
            have heF := hρF.xi.2.1
            have hfr : ∀ w, w ∈ fr (.Xi m e) e → Lt w (.Psi π A) := fun w hw => by
              refine hF w ?_
              simp only [parF, List.mem_append]
              refine Or.inr ?_
              rw [fr]
              simp only [Lt.irrefl, ↓reduceIte]
              exact hw
            exact inC_of_fr_lt heF hρF hy heF heF (xi_selfY hρF) (Or.inr hyρ) (Or.inl rfl) hfr
    · exact lt_psi_psi_same.mpr (harg a rfl)
    · have hne : ρ ≠ π := fun e => Lt.ne hπρ e.symm
      exact (lt_psi_psi_gtT (β := a) (γ := A) hlρ hne hπρ).mpr
        ((lt_psi_psi_gtT (β := a) (γ := X) hlρ hne hπρ).mp hxt)

/-- `σ` への崩壊 `Ψ_σ(B)` への一歩：`z < σ` で、成分の前線が `Ψ_σ(B)` 未満、`z = Ψ_ρ(b)`（`ρ < σ`）なら
    `ρ < Ψ_σ(B)`、`z = Ψ_σ(b)` なら `b < B`、のとき `z < Ψ_σ(B)` -/
theorem coll_step {σ B z : Tm} (hy : WNF (.Psi σ B)) (hz : WNF z) (hzσ : Lt z σ)
    (hF : ∀ w, w ∈ parF z → Lt w (.Psi σ B))
    (hk : ∀ ρ b, z = .Psi ρ b → Lt ρ σ → Lt ρ (.Psi σ B))
    (harg : ∀ b, z = .Psi σ b → Lt b B) : Lt z (.Psi σ B) := by
  have hP := hy.psi
  have hσ := hP.piF
  have hT := hP.tgt
  have hlev : lev z ≤ lev σ := lev_le_of_lt_gen hzσ
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  cases z with
  | zero => exact zero_lt (by intro e; cases e)
  | M k => exact M_lt_psi (by simp only [lev] at hl; omega)
  | plus a b => exact (lt_plus_prin_iffY hz rfl).mpr (hF a (by simp [parF]))
  | Om e =>
    rcases hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp hzσ)
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp hzσ)
    · exact (lt_om_OF' (Or.inr ⟨n, p, B, rfl⟩) (by simp only [lev]; exact hσ.xi.1)).mpr
        (hF e (by simp [parF]))
  | Xi j b =>
    simp only [lev] at hl
    obtain ⟨hj, hbF, -, hbC⟩ := hz.xi
    have hgt : cmp σ (.Xi j b) = .gt := by
      rw [swapY hz hσ]
      have : cmp (.Xi j b) σ = .lt := hzσ
      rw [this]; rfl
    refine (lt_xi_psi_iff (π := σ) (γ := B) (f := b) (n := j) hl.symm).mpr ⟨hgt, ?_⟩
    refine (baseOf_xi_iff j b _).mpr ⟨kTerm_lt_psi hj hl.symm, ?_⟩
    have hyM : Lt (.Psi σ B) (.M j) := lt_of_lev_lt' (by simp only [lev]; omega)
    exact inC_of_fr_lt hbF (WNF.M' hj) hy hbF hbF hbC (Or.inr hyM) (Or.inl rfl)
      (fun w hw => hF w hw)
  | Psi ρ a =>
    have hQ := hz.psi
    have hρF := hQ.piF
    have hlρ : lev ρ = lev σ := by simpa [lev] using hl
    rcases triY hρF hσ with hρσ | rfl | hσρ
    · exact lt_transY hz hρF hy (lt_psi_targetY hz) (hk ρ a rfl hρσ)
    · exact lt_psi_psi_same.mpr (harg a rfl)
    · have hne : ρ ≠ σ := fun e => Lt.ne hσρ e.symm
      exact (lt_psi_psi_gtT (β := a) (γ := B) hlρ hne hσρ).mpr
        (not_base_of_lt_tgtY hz hσ hT hlρ hσρ hzσ)

/-! ### 共終性の帰納法 -/

theorem seq_mono_le {y : Nat → Tm} (hyF : ∀ n, WNF (y n)) (hm : ∀ n, Lt (y n) (y (n + 1)))
    {m n : Nat} (h : m ≤ n) : Le (y m) (y n) := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ ih => exact Or.inr (lt_of_le_of_ltY (hyF _) (hyF _) (hyF _) ih (hm _))

/-- 有限個の元の上界 -/
theorem exists_bound {y : Nat → Tm} {P : Tm → Prop} [DecidablePred P] (hyF : ∀ n, WNF (y n))
    (hm : ∀ n, Lt (y n) (y (n + 1))) :
    ∀ l : List Tm, (∀ w, w ∈ l → WNF w) → (∀ w, w ∈ l → P w → ∃ n, Lt w (y n)) →
      ∃ N, ∀ w, w ∈ l → P w → Lt w (y N)
  | [], _, _ => ⟨0, fun w hw => by cases hw⟩
  | a :: l, hF, h => by
    obtain ⟨N, hN⟩ := exists_bound (P := P) hyF hm l (fun w hw => hF w (List.mem_cons_of_mem _ hw))
      fun w hw => h w (List.mem_cons_of_mem _ hw)
    by_cases hP : P a
    · obtain ⟨N', hN'⟩ := h a List.mem_cons_self hP
      refine ⟨max N N', fun w hw hwP => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact lt_of_lt_of_leY (hF _ hw) (hyF N') (hyF _) hN'
          (seq_mono_le hyF hm (Nat.le_max_right _ _))
      · exact lt_of_lt_of_leY (hF w hw) (hyF N) (hyF _) (hN w hw' hwP)
          (seq_mono_le hyF hm (Nat.le_max_left _ _))
    · exact ⟨N, fun w hw hwP => by
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact absurd hwP hP
        · exact hN w hw' hwP⟩

/-- `ω` 型の共終性の帰納法：成分（`t` 未満のもの）が `y N` 未満なら `x` もどれかの `y m` 未満、を
    示せば、`t` 未満の項は全てどれかの `y n` 未満 -/
theorem cof_nat {t : Tm} {y : Nat → Tm} (hyF : ∀ n, WNF (y n)) (hm : ∀ n, Lt (y n) (y (n + 1)))
    (hstep : ∀ x, WNF x → Lt x t → ∀ N, (∀ w, w ∈ parL x → Lt w t → Lt w (y N)) →
      ∃ m, Lt x (y m)) :
    ∀ x, WNF x → Lt x t → ∃ n, Lt x (y n) := by
  intro x
  induction x using size_induction with
  | h x ih =>
  intro hx hxt
  obtain ⟨N, hN⟩ := exists_bound (P := fun w => Lt w t) hyF hm (parL x)
    (fun w hw => hx.of_mem_subs (parL_sub hw).1)
    (fun w hw hwt => ih w (parL_sub hw).2 (hx.of_mem_subs (parL_sub hw).1) hwt)
  exact hstep x hx hxt N hN

end MahloOCF.FS
