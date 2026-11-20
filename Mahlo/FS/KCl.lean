import Mahlo.FS.XiIter

/-! 閉じた点の探索（`maxCl`・`frCl`）の仕様と、見える閉じた点が全て与えられた点以下の項（`CF`）。

閉じた点は `x` 以上の節点だけを通って見えるもの（`selfVis`）に限るので、成分の所属（`inC_of_selfVis`）が
受け継がれる。外に足す型の対角化の種（`a2Seed`：目標の前線の中で見える `Ψ_σ(·)` の最大のもの）に使う。 -/

namespace MahloOCF.FS

open Tm

/-! ### `frB` と `fr` -/

theorem frB_eq_fr (R : Tm) : ∀ x : Tm, frB R x = fr R x
  | .zero => rfl
  | .M _ => rfl
  | .plus a b => by rw [frB, fr, frB_eq_fr R a, frB_eq_fr R b]
  | .Om a => by rw [frB, fr, frB_eq_fr R a]
  | .Xi m a => by
    rw [frB, fr, frB_eq_fr R a]
    by_cases h : Lt (.Xi m a) R
    · rw [if_pos (ltB_iff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (ltB_iff.mp h')), if_neg h]
  | .Psi p a => by
    rw [frB, fr, frB_eq_fr R p, frB_eq_fr R a]
    by_cases h : Lt (.Psi p a) R
    · rw [if_pos (ltB_iff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (ltB_iff.mp h')), if_neg h]

/-! ### `selfVis` -/

theorem selfVis_self : ∀ {x : Tm}, ((∃ m a, x = .Xi m a) ∨ ∃ p a, x = .Psi p a) → selfVis x x = true := by
  rintro x (⟨m, a, rfl⟩ | ⟨p, a, rfl⟩) <;> simp [selfVis]

theorem le_leB {a b : Tm} (h : Le a b) : leB a b = true := by
  rw [leB_iff]
  rcases h with rfl | h
  · rw [cmp_self]; decide
  · have h' : cmp a b = .lt := h
    rw [h']; decide

theorem selfVis_mem {w : Tm} : ∀ {e : Tm}, selfVis w e = true → w ∈ subs e
  | .zero, h | .M _, h => by simp [selfVis] at h
  | .plus a b, h => by
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · exact subs_plus_l (selfVis_mem h)
    · exact subs_plus_r (selfVis_mem h)
  | .Om a, h => subs_om (selfVis_mem (e := a) h)
  | .Xi m a, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨-, h⟩
    · exact self_mem_subs _
    · exact subs_xi (selfVis_mem h)
  | .Psi p a, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨-, h | h⟩
    · exact self_mem_subs _
    · exact subs_psi_p (selfVis_mem h)
    · exact subs_psi_a (selfVis_mem h)

/-- `x` が `e` の中に `x` 以上の節点だけを通って現れるなら、`e ∈ C(g, d)` から `x ∈ C(g, d)` -/
theorem inC_of_selfVis {x g d : Tm} (hx : WNF x) (hd : Cut d) : ∀ {e : Tm}, WNF e → selfVis x e = true →
    inC e g d = true → inC x g d = true
  | .zero, _, h, _ | .M _, _, h, _ => by simp [selfVis] at h
  | .plus a b, he, h, hC => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at hC
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · exact inC_of_selfVis hx hd ha h hC.1
    · exact inC_of_selfVis hx hd hb h hC.2
  | .Om a, he, h, hC => by
    rw [inC_om] at hC
    exact inC_of_selfVis hx hd he.om.1 h hC
  | .Xi m a, he, h, hC => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · rw [← h]; exact hC
    · have hle : Le x (.Xi m a) := le_of_ne_gtY hx he (leB_iff.mp h1)
      rcases inC_xi_iff.mp hC with h3 | ⟨h3, -⟩
      · exact inC_of_lt_cut hd g hx (hd.le hx he hle h3)
      · exact inC_of_selfVis hx hd he.xi.2.1 h2 h3
  | .Psi p a, he, h, hC => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · rw [← h]; exact hC
    · have hle : Le x (.Psi p a) := le_of_ne_gtY hx he (leB_iff.mp h1)
      have hP := he.psi
      rcases inC_psi_iff.mp hC with h3 | ⟨h3, h4, -⟩
      · exact inC_of_lt_cut hd g hx (hd.le hx he hle h3)
      · rcases h2 with h2 | h2
        · exact inC_of_selfVis hx hd hP.piF h2 h3
        · exact inC_of_selfVis hx hd hP.aF h2 h4

/-- 見える `R` 未満の節点は、前線の元以下 -/
theorem selfVis_fr {w R : Tm} (hwF : WNF w) (hw : Lt w R) : ∀ {e : Tm}, WNF e → selfVis w e = true →
    ∃ u, u ∈ fr R e ∧ Le w u
  | .zero, _, h | .M _, _, h => by simp [selfVis] at h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw ha h
      exact ⟨u, by rw [fr, List.mem_append]; exact Or.inl hu, hle⟩
    · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hb h
      exact ⟨u, by rw [fr, List.mem_append]; exact Or.inr hu, hle⟩
  | .Om a, he, h => by
    obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw he.om.1 (show selfVis w a = true from h)
    exact ⟨u, by rw [fr]; exact hu, hle⟩
  | .Xi m a, he, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    by_cases h1 : Lt (.Xi m a) R
    · refine ⟨.Xi m a, by simp [fr, h1], ?_⟩
      rcases h with e | ⟨h2, -⟩
      · exact Or.inl e.symm
      · exact le_of_ne_gtY hwF he (leB_iff.mp h2)
    · rcases h with e | ⟨-, h2⟩
      · exact absurd (e ▸ hw) h1
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw he.xi.2.1 h2
        exact ⟨u, by rw [fr]; simp only [h1, ↓reduceIte]; exact hu, hle⟩
  | .Psi p a, he, h => by
    have hP := he.psi
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    by_cases h1 : Lt (.Psi p a) R
    · refine ⟨.Psi p a, by simp [fr, h1], ?_⟩
      rcases h with e | ⟨h2, -⟩
      · exact Or.inl e.symm
      · exact le_of_ne_gtY hwF he (leB_iff.mp h2)
    · have hmem : ∀ u, u ∈ fr R p ∨ u ∈ fr R a → u ∈ fr R (.Psi p a) := fun u hu => by
        rw [fr]
        simp only [h1, ↓reduceIte, List.mem_append]
        exact hu
      rcases h with e | ⟨-, h2 | h2⟩
      · exact absurd (e ▸ hw) h1
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hP.piF h2
        exact ⟨u, hmem u (Or.inl hu), hle⟩
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hP.aF h2
        exact ⟨u, hmem u (Or.inr hu), hle⟩

/-- 前線の元の中で見える節点は、もとの項の中で見える -/
theorem selfVis_of_fr {w u R : Tm} (hR : WNF R) (hwF : WNF w) (hv : selfVis w u = true) (hle : Le w u) :
    ∀ {e : Tm}, WNF e → u ∈ fr R e → selfVis w e = true
  | .zero, _, h | .M _, _, h => by simp [fr] at h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [fr, List.mem_append] at h
    simp only [selfVis, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (selfVis_of_fr hR hwF hv hle ha h)
    · exact Or.inr (selfVis_of_fr hR hwF hv hle hb h)
  | .Om a, he, h => by
    rw [fr] at h
    show selfVis w a = true
    exact selfVis_of_fr hR hwF hv hle he.om.1 h
  | .Xi m a, he, h => by
    rw [fr] at h
    by_cases h1 : Lt (.Xi m a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hv
    · simp only [h1, ↓reduceIte] at h
      have hu := he.xi.2.1.of_mem_subs (fr_spec h).1
      have h2 : Lt w R := lt_of_le_of_ltY hwF hu hR hle (fr_spec h).2
      have h3 : Lt w (.Xi m a) := lt_of_lt_of_leY hwF hR he h2 (le_of_not_ltY he hR h1)
      simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨le_leB (Or.inr h3), selfVis_of_fr hR hwF hv hle he.xi.2.1 h⟩
  | .Psi p a, he, h => by
    have hP := he.psi
    rw [fr] at h
    by_cases h1 : Lt (.Psi p a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hv
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have hup : ∀ {q : Tm}, WNF q → u ∈ fr R q → leB w (.Psi p a) = true := fun hq hu' => by
        have hu := hq.of_mem_subs (fr_spec hu').1
        have h2 : Lt w R := lt_of_le_of_ltY hwF hu hR hle (fr_spec hu').2
        exact le_leB (Or.inr (lt_of_lt_of_leY hwF hR he h2 (le_of_not_ltY he hR h1)))
      simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
      rcases h with h | h
      · exact Or.inr ⟨hup hP.piF h, Or.inl (selfVis_of_fr hR hwF hv hle hP.piF h)⟩
      · exact Or.inr ⟨hup hP.aF h, Or.inr (selfVis_of_fr hR hwF hv hle hP.aF h)⟩

/-! ### `maxOpt`・`maxCl` -/

theorem maxOpt_cases {P Q : Option Tm} {x : Tm} (h : maxOpt P Q = some x) : P = some x ∨ Q = some x := by
  unfold maxOpt at h
  split at h
  · exact Or.inr h
  · exact Or.inl h
  · simp only [Option.some.injEq] at h
    split at h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h])

theorem maxOpt_ge_l {P Q : Option Tm} {p : Tm} (hP : P = some p) (_hp : WNF p)
    (hQ : ∀ q, Q = some q → WNF q) : ∃ x, maxOpt P Q = some x ∧ Le p x := by
  subst hP
  cases Q with
  | none => exact ⟨p, rfl, Or.inl rfl⟩
  | some q =>
    by_cases h : ltB p q = true
    · exact ⟨q, by simp [maxOpt, h], Or.inr (ltB_iff.mp h)⟩
    · exact ⟨p, by simp [maxOpt, h], Or.inl rfl⟩

theorem maxOpt_ge_r {P Q : Option Tm} {q : Tm} (hQ : Q = some q) (hq : WNF q)
    (hP : ∀ p, P = some p → WNF p) : ∃ x, maxOpt P Q = some x ∧ Le q x := by
  subst hQ
  cases P with
  | none => exact ⟨q, rfl, Or.inl rfl⟩
  | some p =>
    by_cases h : ltB p q = true
    · exact ⟨q, by simp [maxOpt, h], Or.inl rfl⟩
    · exact ⟨p, by simp [maxOpt, h], le_of_not_ltY (hP p rfl) hq fun h' => h (ltB_iff.mpr h')⟩

/-- 閉じた点の探索の仕様 -/
theorem maxCl_spec {cl : Tm → Bool} {ub G : Tm} : ∀ {e : Tm}, maxCl cl ub e = some G →
    G ∈ subs e ∧ cl G = true ∧ leB G ub = true ∧ selfVis G ub = true ∧
      ((∃ m a, G = .Xi m a) ∨ ∃ p a, G = .Psi p a)
  | .zero, h | .M _, h => by simp [maxCl] at h
  | .plus a b, h => by
    rcases maxOpt_cases h with h | h
    · obtain ⟨h1, h2⟩ := maxCl_spec h
      exact ⟨subs_plus_l h1, h2⟩
    · obtain ⟨h1, h2⟩ := maxCl_spec h
      exact ⟨subs_plus_r h1, h2⟩
  | .Om a, h => by
    obtain ⟨h1, h2⟩ := maxCl_spec (e := a) h
    exact ⟨subs_om h1, h2⟩
  | .Xi m' a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Option.some.injEq] at hc h
        subst h
        exact ⟨self_mem_subs _, hc.1.1, hc.1.2, hc.2, Or.inl ⟨m', a, rfl⟩⟩
      · cases h
    · obtain ⟨h1, h2⟩ := maxCl_spec h
      exact ⟨subs_xi h1, h2⟩
  | .Psi p a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Option.some.injEq] at hc h
        subst h
        exact ⟨self_mem_subs _, hc.1.1, hc.1.2, hc.2, Or.inr ⟨p, a, rfl⟩⟩
      · cases h
    · rcases maxOpt_cases h with h | h
      · obtain ⟨h1, h2⟩ := maxCl_spec h
        exact ⟨subs_psi_p h1, h2⟩
      · obtain ⟨h1, h2⟩ := maxCl_spec h
        exact ⟨subs_psi_a h1, h2⟩

theorem maxCl_wnf {cl : Tm → Bool} {ub e : Tm} (he : WNF e) (G : Tm) (h : maxCl cl ub e = some G) :
    WNF G :=
  he.of_mem_subs (maxCl_spec h).1

/-- `maxCl` は見える閉じた点以上 -/
theorem maxCl_ge {cl : Tm → Bool} {ub w : Tm} (hn : (∃ m a, w = .Xi m a) ∨ ∃ p a, w = .Psi p a)
    (hwF : WNF w) (hwc : cl w = true) (hle : leB w ub = true) (hv : selfVis w ub = true) :
    ∀ {e : Tm}, WNF e → w ∈ subs e → ∃ G, maxCl cl ub e = some G ∧ Le w G
  | .zero, _, h | .M _, _, h => by
    simp only [subs, List.mem_singleton] at h
    rcases hn with ⟨m, a, e⟩ | ⟨p, a, e⟩ <;> rw [e] at h <;> cases h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · rcases hn with ⟨m, a', e⟩ | ⟨p, a', e⟩ <;> cases e
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv ha h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG (maxCl_wnf ha G hG) (maxCl_wnf hb)
      refine ⟨x, hx, le_transY hwF (maxCl_wnf ha G hG) (he.of_mem_subs ?_) hl hl'⟩
      rcases maxOpt_cases hx with h' | h'
      · exact subs_plus_l (maxCl_spec h').1
      · exact subs_plus_r (maxCl_spec h').1
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hb h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf hb G hG) (maxCl_wnf ha)
      refine ⟨x, hx, le_transY hwF (maxCl_wnf hb G hG) (he.of_mem_subs ?_) hl hl'⟩
      rcases maxOpt_cases hx with h' | h'
      · exact subs_plus_l (maxCl_spec h').1
      · exact subs_plus_r (maxCl_spec h').1
  | .Om a, he, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · rcases hn with ⟨m, a', e⟩ | ⟨p, a', e⟩ <;> cases e
    · show ∃ G, maxCl cl ub a = some G ∧ Le w G
      exact maxCl_ge hn hwF hwc hle hv he.om.1 h
  | .Xi m a, he, h => by
    have haF := he.xi.2.1
    have hr : ∀ x, maxCl cl ub (.Xi m a) = some x → x ∈ subs (.Xi m a) :=
      fun x hx => (maxCl_spec hx).1
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · have e1 : (if cl (.Xi m a) && leB (.Xi m a) ub && selfVis (.Xi m a) ub then some (.Xi m a)
          else none) = some (Tm.Xi m a) := by simp [hwc, hle, hv]
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l e1 he (maxCl_wnf haF)
      exact ⟨x, hx, hl'⟩
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv haF h
      have hw0 : ∀ q, (if cl (.Xi m a) && leB (.Xi m a) ub && selfVis (.Xi m a) ub
          then some (.Xi m a) else none) = some q → WNF q := fun q hp => by
        split at hp
        · cases hp; exact he
        · cases hp
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf haF G hG) hw0
      exact ⟨x, hx, le_transY hwF (maxCl_wnf haF G hG) (he.of_mem_subs (hr x hx)) hl hl'⟩
  | .Psi p a, he, h => by
    have hP := he.psi
    have hr : ∀ x, maxCl cl ub (.Psi p a) = some x → x ∈ subs (.Psi p a) :=
      fun x hx => (maxCl_spec hx).1
    have hw3 : ∀ q, maxOpt (maxCl cl ub p) (maxCl cl ub a) = some q → WNF q := by
      intro q h'
      rcases maxOpt_cases h' with h'' | h''
      · exact maxCl_wnf hP.piF q h''
      · exact maxCl_wnf hP.aF q h''
    have hw0 : ∀ q, (if cl (.Psi p a) && leB (.Psi p a) ub && selfVis (.Psi p a) ub
        then some (.Psi p a) else none) = some q → WNF q := fun q hp => by
      split at hp
      · cases hp; exact he
      · cases hp
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hlast : ∀ {G : Tm}, WNF G → Le w G → maxOpt (maxCl cl ub p) (maxCl cl ub a) = some G →
        ∃ G', maxCl cl ub (.Psi p a) = some G' ∧ Le w G' := fun hGF hl hG => by
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG hGF hw0
      exact ⟨x, hx, le_transY hwF hGF (he.of_mem_subs (hr x hx)) hl hl'⟩
    rcases h with rfl | h | h
    · have e1 : (if cl (.Psi p a) && leB (.Psi p a) ub && selfVis (.Psi p a) ub then some (.Psi p a)
          else none) = some (Tm.Psi p a) := by simp [hwc, hle, hv]
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l e1 he hw3
      exact ⟨x, hx, hl'⟩
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hP.piF h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG (maxCl_wnf hP.piF G hG) (maxCl_wnf hP.aF)
      exact hlast (hw3 x hx) (le_transY hwF (maxCl_wnf hP.piF G hG) (hw3 x hx) hl hl') hx
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hP.aF h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf hP.aF G hG) (maxCl_wnf hP.piF)
      exact hlast (hw3 x hx) (le_transY hwF (maxCl_wnf hP.aF G hG) (hw3 x hx) hl hl') hx

theorem foldr_maxOpt_spec {f : Tm → Option Tm} {x : Tm} : ∀ {l : List Tm},
    (l.map f).foldr maxOpt none = some x → ∃ e, e ∈ l ∧ f e = some x
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.map_cons, List.foldr_cons] at h
    rcases maxOpt_cases h with h' | h'
    · exact ⟨a, List.mem_cons_self, h'⟩
    · obtain ⟨e, he, hf⟩ := foldr_maxOpt_spec h'
      exact ⟨e, List.mem_cons_of_mem _ he, hf⟩

theorem foldr_maxOpt_ge {f : Tm → Option Tm} {G : Tm} : ∀ {l : List Tm} {e : Tm},
    (∀ e', e' ∈ l → ∀ q, f e' = some q → WNF q) → e ∈ l → f e = some G →
    ∃ x, (l.map f).foldr maxOpt none = some x ∧ Le G x
  | a :: l, e, hf, he, h => by
    simp only [List.map_cons, List.foldr_cons]
    have hw : ∀ q, (l.map f).foldr maxOpt none = some q → WNF q := fun q hq => by
      obtain ⟨e', he', hf'⟩ := foldr_maxOpt_spec hq
      exact hf e' (List.mem_cons_of_mem _ he') q hf'
    rcases List.mem_cons.mp he with rfl | he'
    · exact maxOpt_ge_l h (hf _ List.mem_cons_self _ h) hw
    · obtain ⟨x, hx, hl⟩ := foldr_maxOpt_ge (fun e'' h'' => hf e'' (List.mem_cons_of_mem _ h'')) he' h
      obtain ⟨x', hx', hl'⟩ := maxOpt_ge_r hx (hw x hx) (hf a List.mem_cons_self)
      have hF' : WNF x' := by
        rcases maxOpt_cases hx' with h' | h'
        · exact hf a List.mem_cons_self x' h'
        · exact hw x' h'
      exact ⟨x', hx', le_transY (hf e (List.mem_cons_of_mem _ he') G h) (hw x hx) hF' hl hl'⟩

/-- 目標の前線の中の閉じた点の最大性 -/
theorem frCl_ge {cl : Tm → Bool} {τ e G' : Tm} (hτ : WNF τ) (he : e ∈ fr τ τ)
    (h : maxCl cl e e = some G') :
    ∃ e', e' ∈ fr τ τ ∧ maxCl cl e' e' = some (frCl cl τ) ∧ Le G' (frCl cl τ) := by
  have hwf : ∀ e', e' ∈ frB τ τ → ∀ q, (fun e => maxCl cl e e) e' = some q → WNF q := fun e' he' q hq => by
    rw [frB_eq_fr] at he'
    exact maxCl_wnf (hτ.of_mem_subs (fr_spec he').1) q hq
  obtain ⟨x, hx, hl⟩ := foldr_maxOpt_ge (f := fun e => maxCl cl e e) hwf (by rw [frB_eq_fr]; exact he) h
  obtain ⟨e', he', hf⟩ := foldr_maxOpt_spec hx
  rw [frB_eq_fr] at he'
  have e1 : frCl cl τ = x := by
    unfold frCl
    rw [hx]
    rfl
  rw [e1]
  exact ⟨e', he', hf, hl⟩

/-- `frCl` は目標の前線の中の閉じた点（なければ `0`） -/
theorem frCl_spec {cl : Tm → Bool} {τ : Tm} :
    frCl cl τ = .zero ∨ ∃ e, e ∈ fr τ τ ∧ maxCl cl e e = some (frCl cl τ) := by
  unfold frCl
  cases h : ((frB τ τ).map (fun e => maxCl cl e e)).foldr maxOpt none with
  | none => exact Or.inl rfl
  | some x =>
    obtain ⟨e, he, hf⟩ := foldr_maxOpt_spec h
    rw [frB_eq_fr] at he
    exact Or.inr ⟨e, he, hf⟩

/-! ### 閉じた点が始点以下の項 -/

/-- `z` の中で見える `z` 以下の閉じた点は全て `G` 以下 -/
def CF (cl : Tm → Bool) (G z : Tm) : Prop :=
  ∀ w, WNF w → cl w = true → Le w z → selfVis w z = true → Le w G

theorem CF.par {cl : Tm → Bool} {G z w' : Tm} (h : CF cl G z) (hz : WNF z) (hw' : w' ∈ parF z) :
    CF cl G w' := by
  intro w hwF hc hle hv
  have hw'F := hz.of_mem_subs (parL_sub (parF_sub_parL hw')).1
  have hlt := parF_lt hz hw'
  have hwz : Lt w z := lt_of_le_of_ltY hwF hw'F hz hle hlt
  refine h w hwF hc (Or.inr hwz) ?_
  cases z with
  | zero | M _ => simp [parF] at hw'
  | plus a b =>
    simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at hw'
    simp only [selfVis, Bool.or_eq_true]
    rcases hw' with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  | Om e =>
    simp only [parF, List.mem_singleton] at hw'
    rw [hw'] at hv
    exact hv
  | Xi j b =>
    have hMF := WNF.M' hz.xi.1
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨le_leB (Or.inr hwz), selfVis_of_fr hMF hwF hv hle hz.xi.2.1 hw'⟩
  | Psi ρ a =>
    have hP := hz.psi
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    simp only [parF, List.mem_append] at hw'
    rcases hw' with h' | h'
    · exact Or.inr ⟨le_leB (Or.inr hwz), Or.inr (selfVis_of_fr hP.piF hwF hv hle hP.aF h')⟩
    · exact Or.inr ⟨le_leB (Or.inr hwz), Or.inl (selfVis_of_fr hP.piF hwF hv hle hP.piF h')⟩

theorem CF.tgt {cl : Tm → Bool} {G ρ a : Tm} (h : CF cl G (.Psi ρ a)) (hz : WNF (.Psi ρ a))
    (hc : cl ρ = false) : CF cl G ρ := by
  intro w hwF hcw hle hv
  have hP := hz.psi
  rcases hle with e | hlt
  · rw [e, hc] at hcw
    cases hcw
  · obtain ⟨u, hu, hle'⟩ := selfVis_fr hwF hlt hP.piF hv
    have huF := hP.piF.of_mem_subs (fr_spec hu).1
    have hwz : Lt w (.Psi ρ a) := lt_of_le_of_ltY hwF huF hz hle' (k2tY hz u hu)
    refine h w hwF hcw (Or.inr hwz) ?_
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨le_leB (Or.inr hwz), Or.inl hv⟩

end MahloOCF.FS
