import Mahlo.WF.Order

/-! 体系全体の整列性 `MahloOCF.wellFounded_isNF`（区別集合の方法。Compact リポジトリの
`Compact/WF/Wmax.lean` と同じ構成）。

* 順序の道具：推移性・三分律（`Order.lean`）と、`GoodY` の補題を体系全体で使う形にしたもの。
* 次の正則項 `nrY`。
* 区別集合と最大区別集合 `Wmax`、`Good α → α ∈ Wmax`。この系では `Ψ` の値が崩壊先にならないので、
  崩壊先をたどる列は `Ψ_ρ(a)`・`ρ`・（`ρ = Ξ_n(p)` なら）`M_n` で終わり、`Good` から `Wmax` が
  無条件に出る（`wmax_of_good`）。
* `Wmax` が全ての項の構成で閉じること（`Ξ_n`・`Ψ_π` は `M_n^+` 以下の範囲 `WK n` の整礎性と、
  引数についての帰納法）、標準形が全て `Wmax` に入ることと整列性。 -/

namespace MahloOCF

open Tm

/-! ## 順序の道具 -/

theorem lt_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c :=
  transY ha hb hc h1 h2

theorem lt_of_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [swapY ha hb, h]
  rfl

theorem le_of_not_ltY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : ¬ Lt a b) : Le b a := by
  rcases triY ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

theorem le_of_ne_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (eqY ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_leY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmY ha hb h

theorem lt_of_lt_of_leY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_transY ha hb hc h1 h2

theorem lt_of_le_of_ltY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_transY ha hb hc h1 h2

theorem le_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leY ha hb hc h1 h2)

theorem le_antisymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leY hb ha h2)

theorem eq_of_cmpP_eqY {x y : Tm} (hx : WNF x) (hy : WNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply eqY hx hy
  rw [cmp_principal hpx hpy, h]

/-! ### `GoodY` の補題を体系全体で -/

macro "memL" : term => `(mem_subsL_self (by simp))

theorem lt_plus_rightY {a b : Tm} (h : WNF (.plus a b)) : Lt b (.plus a b) :=
  (goodYL (wnf_list1 h)).lt_plus_right memL

/-- 主要項 `x` について `x < a + b` ⟺ `x ≤ a` -/
theorem lt_prin_plus_iffY {x a b : Tm} (hx : WNF x) (hxp : isPrincipal x = true)
    (h : WNF (.plus a b)) : Lt x (.plus a b) ↔ Le x a := by
  obtain ⟨ha, -, hap, hb0⟩ := h.plus
  have hL : Lt x (.plus a b) ↔ cmpP x a ≠ .gt := by
    unfold Lt
    rw [cmp_eq, summands_principal hxp, summands_plus]
    cases e : cmpP x a with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e]
      cases hs : summands b with
      | nil => exact absurd hs (summands_ne_nil hb0)
      | cons _ _ => rw [cmpList_nil_cons]; simp
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
  rw [hL]
  constructor
  · intro h'
    exact le_of_ne_gtY hx ha (by rwa [cmp_principal hxp hap])
  · intro h'
    rw [← cmp_principal hxp hap]
    exact ne_gt_of_le h'

theorem lt_plus_plus_neY {a b a' b' : Tm} (h : WNF (.plus a b)) (h' : WNF (.plus a' b'))
    (hne : a ≠ a') : Lt (.plus a b) (.plus a' b') ↔ Lt a a' := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  obtain ⟨ha', -, hap', -⟩ := h'.plus
  have e : cmpP a a' ≠ .eq := fun e => hne (eq_of_cmpP_eqY ha ha' hap hap' e)
  rw [lt_principal_iff hap hap']
  unfold Lt
  rw [cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_ne _ _ e]

theorem lt_om_selfY {a : Tm} (h : WNF (.Om a)) : Lt a (.Om a) :=
  (goodYL (wnf_list1 h)).lt_om_selfS a memL

theorem lt_OF_omY {X e : Tm} (hX : IsOF X) (hXF : WNF X) (he : WNF e) :
    Lt X (.Om e) ↔ Lt X e :=
  (goodYL (wnf_list2 hXF he)).lt_OF_omS hX memL memL

theorem lt_psiOm_omY {c β e : Tm} (hψ : WNF (.Psi (.Om c) β)) (he : WNF e) :
    Lt (.Psi (.Om c) β) (.Om e) ↔ Le c e :=
  (goodYL (wnf_list2 hψ he)).lt_psiOm_omS memL memL

theorem lt_OF_psiOmY {X c β : Tm} (hX : IsOF X) (hXF : WNF X) (hψ : WNF (.Psi (.Om c) β)) :
    Lt X (.Psi (.Om c) β) ↔ Lt X c :=
  (goodYL (wnf_list2 hXF hψ)).lt_OF_psiOmS hX memL memL

theorem le_psiOmY {c β : Tm} (hψ : WNF (.Psi (.Om c) β)) : Le c (.Psi (.Om c) β) :=
  (goodYL (wnf_list1 hψ)).le_psiOm memL

theorem le_om_of_leY {a b : Tm} (h : Le a b) : Le (.Om a) (.Om b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (lt_om_iffG.mpr h)

theorem fr_leY {R : Tm} (hR : WNF R) {x w : Tm} (hx : WNF x) (hw : w ∈ fr R x) : Le w x :=
  (goodYL (wnf_list2 hR hx)).fr_le memL memL hw

theorem fr_subY {R R' : Tm} (hR : WNF R) (hR' : WNF R') (hle : Le R' R) {x w : Tm}
    (hx : WNF x) (hw : w ∈ fr R x) (hwR : Lt w R') : w ∈ fr R' x :=
  fr_subG (fun _ hv h => lt_of_lt_of_leY (hx.of_mem_subs hv) hR' hR h hle) hw hwR

/-- `Ψ_π(γ)` の崩壊の性質 -/
theorem coll_psiY {π γ : Tm} (ht : WNF (.Psi π γ)) {z : Tm} (hz : WNF z)
    (hin : inC z γ (.Psi π γ) = true) (hlt : Lt z π) : Lt z (.Psi π γ) :=
  (goodYL (wnf_list2 ht hz)).coll_psiS memL z memL hin hlt

theorem base_selfY {κ β : Tm} (h : WNF (.Psi κ β)) : baseOf κ (.Psi κ β) = true :=
  (goodYL (wnf_list1 h)).base_self memL

theorem xi_selfY {m : Nat} {f : Tm} (h : WNF (.Xi m f)) : inC f f (.Xi m f) = true :=
  (goodYL (wnf_list1 h)).xi_self memL

theorem not_base_of_lt_tgtY {κ β π : Tm} (hz : WNF (.Psi κ β)) (hπ : WNF π) (hπT : IsTgt π)
    (hl : lev κ = lev π) (hπκ : Lt π κ) (h : Lt (.Psi κ β) π) :
    baseOf π (.Psi κ β) = false :=
  (goodYL (wnf_list2 hz hπ)).not_base_of_lt_tgt memL memL hπT hl hπκ h

theorem baseOf_om_psiOmY {c c' d β : Tm} (hq : WNF (.Psi (.Om c) c')) (hψ : WNF (.Psi (.Om d) β))
    (hcd : cmp c d ≠ .gt) : baseOf (.Om c) (.Psi (.Om d) β) = true :=
  (goodYL (wnf_list2 hq hψ)).baseOf_om_psiOmS (c' := c') memL memL hcd

theorem one_leY {c : Tm} (hc : WNF c) (h0 : c ≠ .zero) : Le one c := by
  rcases triY WNF.one hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exfalso
    cases hs : summands c with
    | nil => exact summands_ne_nil h0 hs
    | cons x xs =>
      have hx := summands_WNF c hc x (by rw [hs]; exact List.mem_cons_self)
      unfold Lt at h
      rw [cmp_eq, hs, summands_one] at h
      rcases cmpList_lt_cases h with e | ⟨e, e'⟩
      · have := cmpP_one_ne_gt hx.1 hx.2
        unfold Lt at *
        rw [eqY_cmpP_swap hx.1 hx.2, e] at this
        exact this rfl
      · cases xs with
        | nil => rw [cmpList_nil_nil] at e'; cases e'
        | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'
where
  eqY_cmpP_swap {x : Tm} (hx : WNF x) (hxp : isPrincipal x = true) :
      cmpP one x = (cmpP x one).swap := by
    rw [← cmp_principal rfl hxp, ← cmp_principal hxp rfl]
    exact swapY hx WNF.one

end MahloOCF

/-! ## 後者と次の正則項 -/

namespace MahloOCF

open Tm

theorem succT_WNF : ∀ {z : Tm}, WNF z → WNF (succT z)
  | .zero, _ => WNF.one
  | .plus a b, hz => by
    obtain ⟨ha, hb, hap, hb0⟩ := hz.plus
    refine WNF.mk_plus ha (succT_WNF hb) hap (succT_ne_zero b) ?_
    intro h rest hs
    rw [summands_succT] at hs
    cases hs' : summands b with
    | nil => exact absurd hs' (summands_ne_nil hb0)
    | cons h' rest' =>
      rw [hs', List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hz.plus_head hs'
  | .M _, hz | .Om _, hz | .Xi _ _, hz | .Psi _ _, hz => by
    refine WNF.mk_plus hz WNF.one rfl (by intro e; cases e) ?_
    intro h rest hs
    rw [summands_one, List.cons.injEq] at hs
    rw [← hs.1, cmp_principal rfl rfl]
    exact cmpP_one_ne_gt hz rfl

theorem omegaFixed_succT (z : Tm) : omegaFixed (succT z) = false := by
  cases z <;> rfl

theorem WNF.om_succT {z : Tm} (hz : WNF z) : WNF (.Om (succT z)) := by
  show isNF (.Om (succT z)) = true
  simp only [isNF, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨succT_WNF hz, omegaFixed_succT z⟩

/-- `z < c` なら `z + 1 ≤ c` -/
theorem succT_leY {z c : Tm} (hz : WNF z) (hc : WNF c) (h : Lt z c) : Le (succT z) c := by
  refine le_of_ne_gtY (succT_WNF hz) hc ?_
  rw [cmp_eq, summands_succT]
  unfold Lt at h
  rw [cmp_eq] at h
  exact cmpList_append_one_ne_gt _ _ (summands_WNF c hc) h

theorem succT_ne_principal (z : Tm) {X : Tm} (hX : isPrincipal X = true) (hX1 : X ≠ one) :
    succT z ≠ X := by
  intro e
  subst e
  cases z <;> simp_all [succT, isPrincipal]

/-- `Ω` の不動点 `X` より小さい `z` について `z + 1 < X` -/
theorem succT_lt_OF {z X : Tm} (hX : IsOF X) (hz : WNF z) (hXF : WNF X) (h : Lt z X) :
    Lt (succT z) X := by
  rcases succT_leY hz hXF h with e | h'
  · exact absurd e (succT_ne_principal z hX.principal hX.ne_one)
  · exact h'

/-- 正則項：`Ψ` の崩壊先と `Ξ_n` の添字 `M_n` -/
def IsRegY (σ : Tm) : Prop :=
  σ = .Om .zero ∨ (∃ c, σ = .Om c ∧ isSucc c = true) ∨ (∃ n, σ = .M n) ∨ (∃ n p, σ = .Xi n p)

theorem IsRegY.M (n : Nat) : IsRegY (.M n) := Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))

theorem IsRegY.tgt {π : Tm} (h : IsTgt π) : IsRegY π := by
  rcases h with e | ⟨c, e, hs⟩ | ⟨n, p, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨c, e, hs⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨n, p, e⟩))

theorem IsRegY.om_succT (z : Tm) : IsRegY (.Om (succT z)) :=
  Or.inr (Or.inl ⟨_, rfl, isSucc_succT z⟩)

/-- 次の正則項：`t` より大きい最小の正則項 -/
def nrY : Tm → Tm
  | .zero => .Om .zero
  | .plus a _ => nrY a
  | .Om a => .Om (succT a)
  | .Psi (.Om c) _ => .Om c
  | t => .Om (succT t)

theorem nrY_M (n : Nat) : nrY (.M n) = .Om (succT (.M n)) := rfl

theorem nrY_om (a : Tm) : nrY (.Om a) = .Om (succT a) := rfl

theorem nrY_xi (n : Nat) (a : Tm) : nrY (.Xi n a) = .Om (succT (.Xi n a)) := rfl

theorem nrY_psiXi (n : Nat) (p β : Tm) :
    nrY (.Psi (.Xi n p) β) = .Om (succT (.Psi (.Xi n p) β)) := rfl

theorem nrY_psiOm (c β : Tm) : nrY (.Psi (.Om c) β) = .Om c := rfl

theorem nrY_principal {t : Tm} (ht : WNF t) : isPrincipal (nrY t) = true := by
  cases t with
  | zero => rfl
  | plus a b => show isPrincipal (nrY a) = true; exact nrY_principal ht.plus.1
  | Psi π β =>
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> rfl
  | _ => rfl

theorem lt_succT_om {t : Tm} (ht : WNF t) : Lt t (.Om (succT t)) :=
  lt_transY ht (succT_WNF ht) (WNF.om_succT ht) (lt_succT t) (lt_om_selfY (WNF.om_succT ht))

theorem nr_specY : ∀ t : Tm, WNF t → WNF (nrY t) ∧ IsRegY (nrY t) ∧ Lt t (nrY t)
  | .zero, _ => ⟨WNF.om_zero, Or.inl rfl, zero_lt (by intro e; cases e)⟩
  | .plus a b, ht => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    obtain ⟨h1, h2, h3⟩ := nr_specY a ha
    exact ⟨h1, h2, (lt_plus_prin_iffY ht (nrY_principal ha)).mpr h3⟩
  | .M n, ht => ⟨WNF.om_succT ht, IsRegY.om_succT _, lt_succT_om ht⟩
  | .Om a, ht => ⟨WNF.om_succT ht.om.1, IsRegY.om_succT _, lt_om_iffG.mpr (lt_succT a)⟩
  | .Xi n a, ht => ⟨WNF.om_succT ht, IsRegY.om_succT _, lt_succT_om ht⟩
  | .Psi π β, ht => by
    rcases ht.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact ⟨WNF.om_zero, Or.inl rfl, lt_psi_targetY ht⟩
    · exact ⟨ht.psi.piF, Or.inr (Or.inl ⟨c, rfl, hs⟩), lt_psi_targetY ht⟩
    · exact ⟨WNF.om_succT ht, IsRegY.om_succT _, lt_succT_om ht⟩

theorem lev_nrY : ∀ {t : Tm}, WNF t → t ≠ .zero → lev (nrY t) = lev t
  | .zero, _, h => absurd rfl h
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    show lev (nrY a) = lev a; exact lev_nrY ha this
  | .M m, _, _ => by simp only [nrY, succT, lev]; omega
  | .Om a, _, _ => by
    show max 1 (lev (succT a)) = max 1 (lev a)
    cases a <;> simp only [succT, lev, one] <;> omega
  | .Xi n a, ht, _ => by
    have := ht.xi.1
    simp only [nrY, succT, lev]; omega
  | .Psi π β, ht, _ => by
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · rfl
    · rfl
    · have := ht.psi.piF.xi.1
      simp only [nrY, succT, lev]; omega

/-- `M_m < Ω_e` ⟺ `M_m < e` -/
theorem lt_M_omY {m : Nat} {e : Tm} (hm : 1 ≤ m) (he : WNF (.Om e)) :
    Lt (.M m) (.Om e) ↔ Lt (.M m) e := by
  have heF := he.om.1
  rcases Nat.lt_trichotomy (lev e) (m + 1) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
  · have hne : e ≠ .M m := fun h => by subst h; exact not_WNF_om_M he
    constructor
    · intro _
      rcases triY (WNF.M' hm) heF with h | h | h
      · exact h
      · exact absurd h.symm hne
      · have := (lt_M_iffY heF hm).mp h; exfalso; omega
    · intro _
      exact (lt_principal_iff rfl rfl).mpr (lt_of_isBotY (by simp only [lev]; omega) rfl rfl rfl he)
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

theorem nr_le_omY : ∀ t : Tm, WNF t → ∀ c : Tm, WNF (.Om c) → Lt t (.Om c) →
    Le (nrY t) (.Om c)
  | .zero, _, c, _, _ => by
    show Le (.Om .zero) (.Om c)
    by_cases hc : c = .zero
    · subst hc; exact Or.inl rfl
    · exact le_om_of_leY (Or.inr (zero_lt hc))
  | .plus a _, ht, c, hc, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_le_omY a ha c hc (lt_transY ha ht hc (lt_plus_leftY ht) h)
  | .M m, ht, _, hc, h =>
    le_om_of_leY (succT_leY ht hc.om.1 ((lt_M_omY ht.M hc).mp h))
  | .Om a, ht, _, hc, h =>
    le_om_of_leY (succT_leY ht.om.1 hc.om.1 (lt_om_iffG.mp h))
  | .Xi n a, ht, _, hc, h =>
    le_om_of_leY (succT_leY ht hc.om.1 ((lt_OF_omY (Or.inl ⟨n, a, rfl⟩) ht hc.om.1).mp h))
  | .Psi π β, ht, c, hc, h => by
    rcases ht.psi_shape with rfl | ⟨d, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact le_om_of_leY ((lt_psiOm_omY ht hc.om.1).mp h)
    · exact le_om_of_leY ((lt_psiOm_omY ht hc.om.1).mp h)
    · exact le_om_of_leY (succT_leY ht hc.om.1
        ((lt_OF_omY (Or.inr ⟨n, p, β, rfl⟩) ht hc.om.1).mp h))

end MahloOCF

namespace MahloOCF

open Tm

theorem nr_lt_OFY : ∀ t : Tm, WNF t → ∀ {X : Tm}, IsOF X → WNF X → Lt t X → Lt (nrY t) X
  | .zero, _, X, hO, hX, _ => (lt_om_OFG hO hX).mpr (zero_lt hO.ne_zero)
  | .plus a _, ht, _, hO, hX, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_lt_OFY a ha hO hX (lt_transY ha ht hX (lt_plus_leftY ht) h)
  | .M n, ht, X, hO, hX, h => (lt_om_OFG hO hX).mpr (succT_lt_OF hO ht hX h)
  | .Om a, ht, X, hO, hX, h =>
    (lt_om_OFG hO hX).mpr (succT_lt_OF hO ht.om.1 hX ((lt_om_OFG hO hX).mp h))
  | .Xi n a, ht, X, hO, hX, h => (lt_om_OFG hO hX).mpr (succT_lt_OF hO ht hX h)
  | .Psi π β, ht, X, hO, hX, h => by
    rcases ht.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · exact (lt_om_OFG hO hX).mpr (zero_lt hO.ne_zero)
    · have hcF := ht.psi.piF.om.1
      have hc : Lt c X := by
        rcases triY hcF hX with h' | e | h'
        · exact h'
        · subst e
          rcases hO with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> simp [isSucc, summands, one] at hs
        · exact absurd ((lt_OF_psiOmY hO hX ht).mpr h') (Lt.asymmY ht hX h)
      exact (lt_om_OFG hO hX).mpr hc
    · exact (lt_om_OFG hO hX).mpr (succT_lt_OF hO ht hX h)

/-- 次の正則項は `t` より大きい正則項の中で最小 -/
theorem nr_leastY (t : Tm) (ht : WNF t) (σ : Tm) (hσ : WNF σ) (hR : IsRegY σ) (h : Lt t σ) :
    Le (nrY t) σ := by
  rcases hR with rfl | ⟨c, rfl, -⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl⟩
  · exact nr_le_omY t ht _ hσ h
  · exact nr_le_omY t ht c hσ h
  · have hm := hσ.M
    refine Or.inr ((lt_M_iffY (nr_specY t ht).1 hm).mpr ?_)
    by_cases h0 : t = .zero
    · subst h0
      show 1 ≤ m
      exact hm
    · rw [lev_nrY ht h0]
      exact (lt_M_iffY ht hm).mp h
  · exact Or.inr (nr_lt_OFY t ht (Or.inl ⟨m, q, rfl⟩) hσ h)

end MahloOCF

/-! ## 区別集合

* `Hull α X` は `C^α(X)`：`{0, M_n} ∪ (X ∩ α)` を `+`、`Ω`、`Ξ_n`（`α < M_n`）、`Ψ_π`（`α < π`）で
  閉じたもの。
* `WPart Y` は `Y` の整礎部分。
* `Dist X`：`X` は区別集合（`X` のある元以下の `α` について、`α` の次の正則項 `nrY α` 未満では、`X` は
  `Hull α X` の整礎部分と一致する）。
* `Wmax` は区別集合全ての合併、`Good α` は `α ∈ C^α(Wmax)` かつ `C^α(Wmax) ∩ α ⊆ Wmax`。 -/

namespace MahloOCF

open Tm

inductive Hull (α : Tm) (X : Tm → Prop) : Tm → Prop where
  | zero : Hull α X .zero
  | M {n : Nat} (hn : 1 ≤ n) : Hull α X (.M n)
  | mem {β : Tm} (hX : X β) (hw : WNF β) (hβ : Lt β α) : Hull α X β
  | plus {a b : Tm} (hw : WNF (.plus a b)) (ha : Hull α X a) (hb : Hull α X b) :
      Hull α X (.plus a b)
  | om {a : Tm} (hw : WNF (.Om a)) (ha : Hull α X a) : Hull α X (.Om a)
  | xi {n : Nat} {a : Tm} (hw : WNF (.Xi n a)) (hα : Lt α (.M n)) (ha : Hull α X a) :
      Hull α X (.Xi n a)
  | psi {π a : Tm} (hw : WNF (.Psi π a)) (hα : Lt α π) (hσ : Hull α X π) (ha : Hull α X a) :
      Hull α X (.Psi π a)

def Rel (Y : Tm → Prop) (x y : Tm) : Prop := Y x ∧ Lt x y

def WPart (Y : Tm → Prop) (β : Tm) : Prop := Y β ∧ Acc (Rel Y) β

def Dist (X : Tm → Prop) : Prop :=
  (∀ β, X β → WNF β) ∧
    ∀ α, WNF α → (∃ δ, X δ ∧ Le α δ) →
      ∀ β, (WPart (Hull α X) β ∧ Lt β (nrY α)) ↔ (X β ∧ Lt β (nrY α))

def Wmax (β : Tm) : Prop := ∃ X, Dist X ∧ X β

def Good (α : Tm) : Prop := Hull α Wmax α ∧ ∀ β, Hull α Wmax β → Lt β α → Wmax β

/-! ### 生成集合 -/

theorem Hull.wf_of {α : Tm} {X : Tm → Prop} {β : Tm} (h : Hull α X β) : WNF β := by
  cases h with
  | zero => exact WNF.zero
  | M hn => exact WNF.M' hn
  | mem _ hw _ => exact hw
  | plus hw _ _ => exact hw
  | om hw _ => exact hw
  | xi hw _ _ => exact hw
  | psi hw _ _ _ => exact hw

/-- 生成集合の元を構成子ごとに写す（元と、添字の条件を与えて） -/
theorem Hull.map {α β : Tm} {X Y : Tm → Prop}
    (hmem : ∀ γ, X γ → WNF γ → Lt γ α → Hull β Y γ)
    (hreg : ∀ σ, WNF σ → IsRegY σ → Lt α σ → Lt β σ) {γ : Tm}
    (h : Hull α X γ) : Hull β Y γ := by
  induction h with
  | zero => exact Hull.zero
  | M hn => exact Hull.M hn
  | mem hX hw hlt => exact hmem _ hX hw hlt
  | plus hw _ _ iha ihb => exact Hull.plus hw iha ihb
  | om hw _ iha => exact Hull.om hw iha
  | xi hw hα _ iha => exact Hull.xi hw (hreg _ (WNF.M' hw.xi.1) (IsRegY.M _) hα) iha
  | psi hw hα _ _ ihσ iha =>
    exact Hull.psi hw (hreg _ hw.psi.piF (IsRegY.tgt hw.psi.tgt) hα) ihσ iha

theorem Hull.mono {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, X γ → WNF γ → Lt γ α → Y γ) {β : Tm} (hb : Hull α X β) :
    Hull α Y β :=
  hb.map (fun γ hX hw hlt => Hull.mem (h γ hX hw hlt) hw hlt) (fun _ _ _ h => h)

theorem Hull.congr {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, WNF γ → Lt γ α → (X γ ↔ Y γ)) (β : Tm) :
    Hull α X β ↔ Hull α Y β :=
  ⟨Hull.mono (fun γ hX hw hlt => (h γ hw hlt).mp hX),
    Hull.mono (fun γ hY hw hlt => (h γ hw hlt).mpr hY)⟩

/-- `α` より大きい正則項は `nrY α` 未満の全ての項より大きい -/
theorem lt_of_lt_nr {α β σ : Tm} (wα : WNF α) (wβ : WNF β) (wσ : WNF σ)
    (hσR : IsRegY σ) (h1 : Lt α σ) (h2 : Lt β (nrY α)) : Lt β σ :=
  lt_of_lt_of_leY wβ (nr_specY α wα).1 wσ h2 (nr_leastY α wα σ wσ hσR h1)

/-- 次の正則項までの範囲でパラメタを上げる -/
theorem Hull.raise {α β : Tm} {X : Tm → Prop} (wα : WNF α) (wβ : WNF β)
    (h1 : Lt α β) (h2 : Lt β (nrY α)) {γ : Tm} (hγ : Hull α X γ) :
    Hull β X γ :=
  hγ.map (fun _ hX hw hlt => Hull.mem hX hw (lt_transY hw wα wβ hlt h1))
    (fun _ wσ hσR hσ => lt_of_lt_nr wα wβ wσ hσR hσ h2)

theorem Hull.lower_aux {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α : Tm}
    (wα : WNF α) : ∀ γ β : Tm, WNF β → Le α β → Hull β X γ →
      Hull α X γ ∨ (X γ ∧ Lt γ β) := by
  intro γ
  induction γ using size_induction with
  | h γ ih =>
    intro β wβ hαβ h
    have conv : ∀ c : Tm, c.size < γ.size → Hull β X c → Hull α X c := by
      intro c hc hcβ
      have wc := hcβ.wf_of
      refine (ih c hc β wβ hαβ hcβ).elim id (fun ⟨hXc, _⟩ => ?_)
      by_cases hca : Lt c α
      · exact Hull.mem hXc wc hca
      · exact (ih c hc c wc (le_of_not_ltY wc wα hca) (HX c hXc)).resolve_right
          (fun ⟨_, h⟩ => Lt.irrefl _ h)
    cases h with
    | zero => exact Or.inl Hull.zero
    | M hn => exact Or.inl (Hull.M hn)
    | mem hX _ hlt => exact Or.inr ⟨hX, hlt⟩
    | plus hw ha hb =>
      exact Or.inl (Hull.plus hw (conv _ (by size_omega) ha) (conv _ (by size_omega) hb))
    | om hw ha => exact Or.inl (Hull.om hw (conv _ (by size_omega) ha))
    | xi hw hβK ha =>
      exact Or.inl (Hull.xi hw (lt_of_le_of_ltY wα wβ (WNF.M' hw.xi.1) hαβ hβK)
        (conv _ (by size_omega) ha))
    | psi hw hβσ hσ ha =>
      exact Or.inl (Hull.psi hw (lt_of_le_of_ltY wα wβ hw.psi.piF hαβ hβσ)
        (conv _ (by size_omega) hσ) (conv _ (by size_omega) ha))

/-- `α ≤ β` なら `C^β(X) ⊆ C^α(X)`（`X` の各元が自分の生成集合に入るとき） -/
theorem Hull.lower {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α β : Tm}
    (wα : WNF α) (wβ : WNF β) (hαβ : Le α β) {γ : Tm} (h : Hull β X γ) :
    Hull α X γ := by
  have wγ := h.wf_of
  refine (Hull.lower_aux HX wα γ β wβ hαβ h).elim id (fun ⟨hX, _⟩ => ?_)
  by_cases hγα : Lt γ α
  · exact Hull.mem hX wγ hγα
  · exact (Hull.lower_aux HX wα γ γ wγ (le_of_not_ltY wγ wα hγα) (HX γ hX)).resolve_right
      (fun ⟨_, h⟩ => Lt.irrefl _ h)

theorem Hull.sub_of_lt_nr {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {β γ : Tm}
    (wβ : WNF β) (wγ : WNF γ) (h : Lt γ (nrY β)) {x : Tm}
    (hx : Hull β X x) : Hull γ X x := by
  rcases triY wγ wβ with h' | rfl | h'
  · exact Hull.lower HX wγ wβ (Or.inr h') hx
  · exact hx
  · exact Hull.raise wβ wγ h' h hx

/-! ### 整礎部分 -/

theorem acc_of_below {Y Z : Tm → Prop} (hY : ∀ x, Y x → WNF x) :
    ∀ β : Tm, Acc (Rel Z) β → WNF β → (∀ x, Y x → Lt x β → Z x) →
      Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    intro wβ hb
    refine Acc.intro β ?_
    intro x hx
    exact ih x ⟨hb x hx.1 hx.2, hx.2⟩ (hY x hx.1)
      (fun x' hx' hx'x => hb x' hx' (lt_transY (hY x' hx') (hY x hx.1) wβ hx'x hx.2))

theorem acc_sub {Y Z : Tm → Prop} (h : ∀ x, Y x → Z x) :
    ∀ β : Tm, Acc (Rel Z) β → Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    exact Acc.intro β (fun x hx => ih x ⟨h x hx.1, hx.2⟩)

theorem WPart.congr {Y Z : Tm → Prop} (h : ∀ x, Y x ↔ Z x) (β : Tm) :
    WPart Y β ↔ WPart Z β :=
  Iff.intro (fun hb => ⟨(h β).mp hb.1, acc_sub (fun x hx => (h x).mpr hx) β hb.2⟩)
    (fun hb => ⟨(h β).mpr hb.1, acc_sub (fun x hx => (h x).mp hx) β hb.2⟩)

theorem WPart.down {Y : Tm → Prop} {β γ : Tm} (hβ : WPart Y β) (hγ : Y γ)
    (h : Lt γ β) : WPart Y γ :=
  ⟨hγ, hβ.2.inv ⟨hγ, h⟩⟩

/-! ### 区別集合 -/

theorem Dist.mem_wf {X : Tm → Prop} (hX : Dist X) {β : Tm} (h : X β) : WNF β :=
  hX.1 β h

theorem Dist.self {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) :
    WPart (Hull γ X) γ := by
  have wγ := hX.mem_wf hγ
  exact ((hX.2 γ wγ ⟨γ, hγ, Or.inl rfl⟩ γ).mpr ⟨hγ, (nr_specY γ wγ).2.2⟩).1

theorem Dist.self_hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) : Hull γ X γ :=
  (hX.self hγ).1

theorem Dist.hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) {β : Tm}
    (wβ : WNF β) : Hull β X γ := by
  have wγ := hX.mem_wf hγ
  by_cases h : Lt γ β
  · exact Hull.mem hγ wγ h
  · exact Hull.lower (fun _ h => hX.self_hull h) wβ wγ (le_of_not_ltY wγ wβ h)
      (hX.self_hull hγ)

theorem Dist.acc {X : Tm → Prop} (hX : Dist X) {δ : Tm} (hδ : X δ) : Acc (Rel X) δ := by
  have wδ := hX.mem_wf hδ
  exact acc_of_below hX.1 δ (hX.self hδ).2 wδ
    (fun x hx hxδ => Hull.mem hx (hX.mem_wf hx) hxδ)

/-- 区別集合どうしの比較（`X` と `Y` に沿った二重の帰納法） -/
theorem dist_claim {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) :
    ∀ δ, X δ → (∃ ε, Y ε ∧ Le δ ε) → Y δ ∧ (∀ ε, Y ε → Lt ε δ → X ε) := by
  intro δ hδ
  induction hX.acc hδ with
  | intro δ _ ihX =>
    intro hδY
    obtain ⟨ε₀, hε₀, hδε₀⟩ := hδY
    have wδ := hX.mem_wf hδ
    have wε₀ := hY.mem_wf hε₀
    have s1 : ∀ x, X x → Lt x δ → Y x := fun x hx hxδ =>
      (ihX x ⟨hx, hxδ⟩ hx
        ⟨ε₀, hε₀, Or.inr (lt_of_lt_of_leY (hX.mem_wf hx) wδ wε₀ hxδ hδε₀)⟩).1
    have key2 : ∀ ε, Acc (Rel Y) ε → Y ε → Lt ε δ → X ε := by
      intro ε hacc'
      induction hacc' with
      | intro ε _ ihY =>
        intro hε hεδ
        have wε := hY.mem_wf hε
        have agree : ∀ γ, WNF γ → Lt γ ε → (X γ ↔ Y γ) := fun γ wγ hγε =>
          Iff.intro (fun hγ => s1 γ hγ (lt_transY wγ wε wδ hγε hεδ))
            (fun hγ => ihY γ ⟨hγ, hγε⟩ hγ (lt_transY wγ wε wδ hγε hεδ))
        have hxε : WPart (Hull ε X) ε :=
          (WPart.congr (Hull.congr agree) ε).mpr (hY.self hε)
        exact ((hX.2 ε wε ⟨δ, hδ, Or.inr hεδ⟩ ε).mp ⟨hxε, (nr_specY ε wε).2.2⟩).1
    have s2 : ∀ ε, Y ε → Lt ε δ → X ε := fun ε hε => key2 ε (hY.acc hε) hε
    refine ⟨?_, s2⟩
    have agree : ∀ γ, WNF γ → Lt γ δ → (X γ ↔ Y γ) := fun γ _ hγδ =>
      Iff.intro (fun hγ => s1 γ hγ hγδ) (fun hγ => s2 γ hγ hγδ)
    have hyδ : WPart (Hull δ Y) δ := (WPart.congr (Hull.congr agree) δ).mp (hX.self hδ)
    exact ((hY.2 δ wδ ⟨ε₀, hε₀, hδε₀⟩ δ).mp ⟨hyδ, (nr_specY δ wδ).2.2⟩).1

theorem dist_agree {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) {α : Tm}
    (wα : WNF α) (hαX : ∃ δ, X δ ∧ Le α δ) (hαY : ∃ ε, Y ε ∧ Le α ε) :
    ∀ β, Lt β (nrY α) → (X β ↔ Y β) := by
  obtain ⟨δ, hδ, hαδ⟩ := hαX
  obtain ⟨ε, hε, hαε⟩ := hαY
  have agree : ∀ γ, WNF γ → Lt γ α → (X γ ↔ Y γ) := fun γ wγ hγα =>
    Iff.intro
      (fun hγ => (dist_claim hX hY γ hγ
        ⟨ε, hε, Or.inr (lt_of_lt_of_leY wγ wα (hY.mem_wf hε) hγα hαε)⟩).1)
      (fun hγ => (dist_claim hY hX γ hγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leY wγ wα (hX.mem_wf hδ) hγα hαδ)⟩).1)
  have hc := Hull.congr agree
  intro β hβ
  exact Iff.intro
    (fun hb => ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mp
      ⟨(WPart.congr hc β).mp ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)
    (fun hb => ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mp
      ⟨(WPart.congr hc β).mpr ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)

/-! ### 最大区別集合 -/

theorem wmax_dist : Dist Wmax := by
  refine ⟨fun β hβ => hβ.elim (fun X h => h.1.mem_wf h.2), ?_⟩
  intro α wα hα β
  obtain ⟨δ, ⟨X₀, hX₀, hδ⟩, hαδ⟩ := hα
  have hnα := nr_specY α wα
  have agreeW : ∀ γ, Lt γ (nrY α) → (Wmax γ ↔ X₀ γ) := by
    intro γ hγ
    refine Iff.intro ?_ (fun h => ⟨X₀, hX₀, h⟩)
    intro hW
    obtain ⟨Y, hY, hγY⟩ := hW
    have wγ := hY.mem_wf hγY
    by_cases hγα : Lt γ α
    · exact (dist_agree hX₀ hY wγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leY wγ wα (hX₀.mem_wf hδ) hγα hαδ)⟩
        ⟨γ, hγY, Or.inl rfl⟩ γ (nr_specY γ wγ).2.2).mpr hγY
    · exact (dist_agree hX₀ hY wα ⟨δ, hδ, hαδ⟩ ⟨γ, hγY, le_of_not_ltY wγ wα hγα⟩ γ hγ).mpr hγY
  have hc : ∀ x, Hull α Wmax x ↔ Hull α X₀ x :=
    Hull.congr (fun γ wγ hγα => agreeW γ (lt_transY wγ wα hnα.1 hγα hnα.2.2))
  rw [WPart.congr hc β, hX₀.2 α wα ⟨δ, hδ, hαδ⟩ β]
  exact Iff.intro (fun h => ⟨(agreeW β h.2).mpr h.1, h.2⟩)
    (fun h => ⟨(agreeW β h.2).mp h.1, h.2⟩)

theorem wmax_wf {β : Tm} (h : Wmax β) : WNF β := wmax_dist.mem_wf h

theorem wmax_self {γ : Tm} (h : Wmax γ) : WPart (Hull γ Wmax) γ := wmax_dist.self h

theorem wmax_hull {γ : Tm} (h : Wmax γ) {β : Tm} (wβ : WNF β) : Hull β Wmax γ :=
  wmax_dist.hull h wβ

theorem wmax_acc {δ : Tm} (h : Wmax δ) : Acc (Rel Wmax) δ := wmax_dist.acc h

theorem HW : ∀ γ, Wmax γ → Hull γ Wmax γ := fun _ h => wmax_dist.self_hull h

/-- `C^β(Wmax)` の元で、`β⁺` 未満の `Wmax` の元以下のものは `Wmax` に入る -/
theorem wmax_bounded {α β δ : Tm} (wβ : WNF β) (hα : Hull β Wmax α) (hδ : Wmax δ)
    (hαδ : Le α δ) (hδβ : Lt δ (nrY β)) : Wmax α := by
  have wδ := wmax_wf hδ
  have wα := hα.wf_of
  have hα' : Hull δ Wmax α := Hull.sub_of_lt_nr HW wβ wδ hδβ hα
  rcases hαδ with e | hlt
  · rw [e]
    exact hδ
  · have hw := WPart.down (wmax_self hδ) hα' hlt
    exact ((wmax_dist.2 δ wδ ⟨δ, hδ, Or.inl rfl⟩ α).mp
      ⟨hw, lt_transY wα wδ (nr_specY δ wδ).1 hlt (nr_specY δ wδ).2.2⟩).1

theorem wmax_good {γ : Tm} (h : Wmax γ) : Good γ :=
  ⟨HW γ h, fun _ hβ hlt =>
    wmax_bounded (wmax_wf h) hβ h (Or.inr hlt) (nr_specY _ (wmax_wf h)).2.2⟩

theorem acc_hull_of_wmax {μ δ : Tm} (hδ : Wmax δ)
    (h : ∀ x, Hull μ Wmax x → Lt x δ → Wmax x) : Acc (Rel (Hull μ Wmax)) δ :=
  acc_of_below (fun _ hx => hx.wf_of) δ (wmax_acc hδ) (wmax_wf hδ) h

/-! ### `Wmax` の拡張 -/

/-- 拡張の仮定：`γ⁺ ≤ α` の `C^γ(Wmax)` の整礎部分（`γ⁺` 未満）は `Wmax` に入る -/
def Hyp (α : Tm) : Prop := ∀ γ, WNF γ → Le (nrY γ) α → ∀ β,
  WPart (Hull γ Wmax) β → Lt β (nrY γ) → Wmax β

def Ext (α β : Tm) : Prop := WPart (Hull α Wmax) β ∧ Lt β (nrY α)

theorem wmax_of_good_hyp {α : Tm} (hG : Good α) (hH : Hyp α) : Wmax α := by
  have wα := hG.1.wf_of
  have hnα := nr_specY α wα
  have accα : ∀ x, Wmax x → Lt x α → Acc (Rel (Hull α Wmax)) x := fun x hx hxα =>
    acc_hull_of_wmax hx (fun x' hx' hx'x =>
      hG.2 x' hx' (lt_transY hx'.wf_of (wmax_wf hx) wα hx'x hxα))
  have agree : ∀ β, Lt β α → (Ext α β ↔ Wmax β) := fun β hβα =>
    ⟨fun hb => hG.2 β hb.1.1 hβα, fun hb => ⟨⟨Hull.mem hb (wmax_wf hb) hβα, accα β hb hβα⟩,
      lt_transY (wmax_wf hb) wα hnα.1 hβα hnα.2.2⟩⟩
  have hYwf : ∀ β, Ext α β → WNF β := fun β hb => hb.1.1.wf_of
  refine ⟨Ext α, ⟨hYwf, ?_⟩,
    ⟨⟨hG.1, Acc.intro α (fun x hx => accα x (hG.2 x hx.1 hx.2) hx.2)⟩, hnα.2.2⟩⟩
  intro γ wγ ⟨ε, hε, hγε⟩ β
  have hnγ := nr_specY γ wγ
  have hnγnα := nr_leastY γ wγ (nrY α) hnα.1 hnα.2.1
    (lt_of_le_of_ltY wγ (hYwf ε hε) hnα.1 hγε hε.2)
  have split : Le (nrY γ) α ∨ Lt α (nrY γ) :=
    (triY hnγ.1 wα).elim (fun h => Or.inl (Or.inr h))
      (fun h => h.elim (fun e => Or.inl (Or.inl e)) Or.inr)
  rcases split with hle | hgt
  · have hγα : Lt γ α := lt_of_lt_of_leY wγ hnγ.1 wα hnγ.2.2 hle
    rw [WPart.congr (Hull.congr (fun x wx hxγ => agree x (lt_transY wx wγ wα hxγ hγα))) β]
    constructor
    · intro hb
      exact ⟨(agree β (lt_of_lt_of_leY hb.1.1.wf_of hnγ.1 wα hb.2 hle)).mpr
        (hH γ wγ hle β hb.1 hb.2), hb.2⟩
    · intro hb
      have wb := hYwf β hb.1
      have hbW := (agree β (lt_of_lt_of_leY wb hnγ.1 wα hb.2 hle)).mp hb.1
      refine ⟨?_, hb.2⟩
      by_cases hβγ : Lt β γ
      · exact ⟨Hull.mem hbW wb hβγ, acc_hull_of_wmax hbW (fun x hx hxβ => wmax_bounded wb
          (Hull.lower HW wb wγ (Or.inr hβγ) hx) hbW (Or.inr hxβ) (nr_specY β wb).2.2)⟩
      · exact ((wmax_dist.2 γ wγ ⟨β, hbW, le_of_not_ltY wb wγ hβγ⟩ β).mpr ⟨hbW, hb.2⟩).1
  · have heqn : nrY γ = nrY α :=
      le_antisymmY hnγ.1 hnα.1 hnγnα (nr_leastY α wα (nrY γ) hnγ.1 hnγ.2.1 hgt)
    have hc : ∀ x, Hull γ (Ext α) x ↔ Hull α Wmax x := by
      rcases triY wγ wα with hγα | rfl | hαγ
      · intro x
        rw [Hull.congr (fun x wx hxγ => agree x (lt_transY wx wγ wα hxγ hγα)) x]
        exact ⟨Hull.raise wγ wα hγα hgt, Hull.lower HW wγ wα (Or.inr hγα)⟩
      · exact Hull.congr (fun x _ hxγ => agree x hxγ)
      · intro x
        exact ⟨Hull.map (fun _ hY _ _ => hY.1.1) (fun _ wσ _ h => lt_transY wα wγ wσ hαγ h),
          Hull.map (fun _ hW hw hlt => Hull.mem ((agree _ hlt).mpr hW) hw
            (lt_transY hw wα wγ hlt hαγ))
            (fun _ wσ hσR h => lt_of_lt_nr wα wγ wσ hσR h (by rw [← heqn]; exact hnγ.2.2))⟩
    rw [WPart.congr hc β, heqn]
    exact ⟨fun hb => ⟨⟨hb.1, hb.2⟩, hb.2⟩, fun hb => ⟨hb.1.1, hb.2⟩⟩

end MahloOCF

/-! ## 生成集合の移し替えと係数についての帰納法 -/

namespace MahloOCF

open Tm

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν ≤ R` なら `C^ν(Wmax)` に入る -/
theorem hull_transfer {θ ν R : Tm} (wν : WNF ν) (wR : WNF R) (hνR : Le ν R) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → Hull ν Wmax x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr
    by_cases hxθ : Lt x θ
    · exact wmax_hull (good x hx hxθ hs) wν
    · cases hx with
      | zero => exact Hull.zero
      | M hn => exact Hull.M hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        exact Hull.plus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)))
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)))
      | om hw ha =>
        exact Hull.om hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)))
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have wK := WNF.M' hw.xi.1
        have hνK : Lt ν (.M n) := lt_of_le_of_ltY wν wR wK hνR
          (lt_of_le_of_ltY wR hw wK (le_of_not_ltY hw wR hnR)
            ((lt_M_iffY hw hw.xi.1).mpr (Nat.le_refl _)))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi π a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have wπ := hw.psi.piF
        have hνσ : Lt ν π := lt_of_le_of_ltY wν wR wπ hνR
          (lt_of_le_of_ltY wR hw wπ (le_of_not_ltY hw wR hnR) (lt_psi_targetY hw))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hM : ∀ {n : Nat}, 1 ≤ n → P (.M n))
    (hplus : ∀ {a b : Tm}, WNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, WNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, WNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {π a : Tm}, WNF (.Psi π a) → Lt a g → P π → P a → P (.Psi π a)) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      P x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr hC
    by_cases hxθ : Lt x θ
    · exact good x hx hxθ hs
    · cases hx with
      | zero => exact hzero
      | M hn => exact hM hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        rw [inC_plus, Bool.and_eq_true] at hC
        exact hplus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)) hC.1)
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)) hC.2)
      | om hw ha =>
        rw [inC_om] at hC
        exact hom hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)) hC)
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have hC' := (inC_xi_iff.mp hC).resolve_left hnR
        exact hxi hw hC'.2 (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)) hC'.1)
      | @psi π a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have hC' := (inC_psi_iff.mp hC).resolve_left hnR
        exact hpsi hw hC'.2.2
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h))
            hC'.1)
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h))
            hC'.2.1)

/-! ### `Wmax` の元の部分 -/

theorem wmax_om_arg {c : Tm} (h : Wmax (.Om c)) : Wmax c := by
  cases (wmax_good h).1 with
  | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
  | om hw hc => exact (wmax_good h).2 c hc (lt_om_selfY hw)

theorem fr_hull_wmax {θ R : Tm}
    (IH : ∀ m, Wmax m → Lt m θ → ∀ w, w ∈ fr R m → Wmax w) :
    ∀ y, Hull θ Wmax y → ∀ w, w ∈ fr R y → Wmax w ∨ Hull θ Wmax w := by
  intro y hy
  induction hy with
  | zero => intro w h; simp [fr] at h
  | M _ => intro w h; simp [fr] at h
  | mem hX _ hlt => intro w h; exact Or.inl (IH _ hX hlt w h)
  | plus _ _ _ iha ihb =>
    intro w h
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact iha w h
    · exact ihb w h
  | om _ _ iha => intro w h; rw [fr] at h; exact iha w h
  | @xi n a hw hα ha iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Xi n a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.xi hw hα ha)
    · simp only [hl, ↓reduceIte] at h
      exact iha w h
  | @psi π a hw hα hσ ha ihσ iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Psi π a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.psi hw hα hσ ha)
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      rcases h with h | h
      · exact ihσ w h
      · exact iha w h

/-- `Wmax` の元の前線の元は `Wmax` に入る -/
theorem fr_wmax {R : Tm} (wR : WNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
  intro x hx
  induction wmax_acc hx with
  | intro x _ ih =>
    intro w hw
    have hG := wmax_good hx
    rcases fr_hull_wmax (fun m hm hmx => ih m ⟨hm, hmx⟩ hm) x hG.1 w hw with h | h
    · exact h
    · rcases fr_leY wR (wmax_wf hx) hw with e | hlt
      · rw [e]; exact hx
      · exact hG.2 w h hlt

/-- `C^β(Wmax)` の元の前線の元で `γ` 未満のものは、`γ` 未満の `C^β(Wmax)` の元が `Wmax` に入るなら
    `Wmax` に入る -/
theorem fr_hull_below {β γ R y : Tm} (wR : WNF R) (hy : Hull β Wmax y)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ) {w : Tm} (hw : w ∈ fr R y) (hwγ : Lt w γ) :
    Wmax w := by
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) y hy w hw with h | h
  · exact h
  · exact MIH w h hwγ

end MahloOCF

/-! ## `Good α → α ∈ Wmax` -/

namespace MahloOCF

open Tm

/-- `(18)` の証明の場合 2：添字 `π ≤ β`（または `M_n ≤ β`）の崩壊 `α < γ`（`γ < π`）を、`γ` の作り方で
    場合を分けて、`Wmax` の元で上から押さえる -/
theorem case_two {β γ α : Tm} (wβ : WNF β) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ)
    (hshape : (∃ n a, α = .Xi n a ∧ Lt γ (.M n) ∧ Le (.M n) β) ∨
      (∃ π a, α = .Psi π a ∧ Lt γ π ∧ Le π β))
    (hα : Hull γ Wmax α) (hαγ : Lt α γ) : Wmax α := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have hnγ := nr_specY γ wγ
  have hαp : isPrincipal α = true := by
    rcases hshape with ⟨n, a, rfl, -⟩ | ⟨π, a, rfl, -⟩ <;> rfl
  have bound : ∀ w, Wmax w → Lt w γ → ¬ Lt w α → Wmax α := fun w hW hwγ hn =>
    wmax_bounded wγ hα hW (le_of_not_ltY (wmax_wf hW) wα hn)
      (lt_transY (wmax_wf hW) wγ hnγ.1 hwγ hnγ.2.2)
  cases hγH with
  | zero => exact absurd hαγ (not_lt_zero _)
  | M hj =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, -⟩ | ⟨π, a, rfl, hγσ, -⟩
    · have h1 := (lt_M_iffY wα hj).mp hαγ
      have h2 := (lt_M_iffY (WNF.M' hj) wα.xi.1).mp hγK
      simp only [lev] at h1 h2
      omega
    · have h1 := (lt_M_iffY wα hj).mp hαγ
      have h2 := lev_le_of_lt_gen hγσ
      simp only [lev] at h1 h2
      omega
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @plus g₁ g₂ hw hg₁ _ =>
    exact wmax_bounded wγ hα (MIH g₁ hg₁ (lt_plus_leftY hw))
      ((lt_prin_plus_iffY wα hαp hw).mp hαγ)
      (lt_transY hw.plus.1 hw hnγ.1 (lt_plus_leftY hw) hnγ.2.2)
  | @om e hw he =>
    have heW := MIH e he (lt_om_selfY hw)
    have hb : Lt e (nrY (.Om e)) := lt_transY hw.om.1 hw hnγ.1 (lt_om_selfY hw) hnγ.2.2
    rcases hshape with ⟨n, a, rfl, -, -⟩ | ⟨π, a, rfl, hγσ, -⟩
    · exact wmax_bounded wγ hα heW
        (Or.inr ((lt_OF_omY (Or.inl ⟨n, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
    · rcases wα.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨m, p, rfl⟩
      · exfalso
        exact not_lt_zero e (lt_om_iffG.mp hγσ)
      · exfalso
        have h1 := (lt_psiOm_omY wα hw.om.1).mp hαγ
        exact not_lt_of_leY wα.psi.piF hw (le_om_of_leY h1) hγσ
      · exact wmax_bounded wγ hα heW
          (Or.inr ((lt_OF_omY (Or.inr ⟨m, p, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
  | @xi j b hw hβK hb =>
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_M_iffY hw wα.xi.1).mp hγK
      have h2 := (lt_M_iffY (WNF.M' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltY (WNF.M' wα.xi.1) wβ (WNF.M' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      have hmj : lev π = j := by
        have h1 := lev_le_of_lt_gen hγσ
        have h2 := (lt_M_iffY wπ hw.xi.1).mp (lt_of_le_of_ltY wπ wβ (WNF.M' hw.xi.1) hσβ hβK)
        simp only [lev] at h1 h2
        omega
      rcases (lt_psi_xiY hmj).mp hαγ with h' | h'
      · exact absurd hγσ (not_lt_of_leY wπ hw (le_of_ne_gtY wπ hw h'))
      · rw [baseOf_xi] at h'
        have hk : (cmp (kTerm (j - 1)) (Tm.Psi π a) == .lt) = true := by
          have := kTerm_lt (n := j) hw.xi.1 wα rfl rfl hmj
          unfold Lt at this; rw [this]; rfl
        rw [hk, Bool.true_and] at h'
        obtain ⟨w, hwfr, hwn⟩ := wit_of_not_inC hw.xi.2.2.2 (fun _ _ h => h) h'
        have hwγ := k2xY hw w hwfr
        exact bound w (fr_hull_below (WNF.M' hw.xi.1) hb MIH hwfr hwγ) hwγ hwn
  | @psi κ b hw hβκ hκ hb =>
    have wκ := hw.psi.piF
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_M_iffY hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltY (WNF.M' wα.xi.1) wβ wκ hKβ hβκ)
      simp only [lev] at h1 h2
      omega
    · exfalso
      have wπ := wα.psi.piF
      have hπκ : Lt π κ := lt_of_le_of_ltY wπ wβ wκ hσβ hβκ
      have hl : lev π = lev κ := by
        have h1 := lev_le_of_lt_gen hπκ
        have h2 := lev_le_of_lt_gen hγσ
        have h3 := lev_le_of_lt_gen hαγ
        simp only [lev] at h2 h3
        omega
      have hne : π ≠ κ := fun e => Lt.ne hπκ e
      have hb1 := (lt_psi_psi_ltT (κ := π) (β := a) (π := κ) (γ := b) hl hne
        (Lt.asymmY wπ wκ hπκ)).mp hαγ
      rw [not_base_of_lt_tgtY hw wπ wα.psi.tgt hl.symm hπκ hγσ] at hb1
      cases hb1

/-! ### 崩壊先をたどる列 -/

/-- `γ` は `η` を添字とする崩壊（`η = M_n` の `Ξ_n(b)`、または `η` を崩壊先とする `Ψ_η(b)`） -/
def IsColl (η γ : Tm) : Prop := (∃ n b, η = .M n ∧ γ = .Xi n b) ∨ ∃ b, γ = .Psi η b

/-- `Ch γ τ`：`τ` は `γ` から崩壊先を 0 回以上たどって得られる（`Ψ_ρ(b)` の次は `ρ`） -/
inductive Ch : Tm → Tm → Prop
  | refl (x : Tm) : Ch x x
  | step {x ρ b : Tm} : Ch x (.Psi ρ b) → Ch x ρ

theorem Ch.wnf {x y : Tm} (h : Ch x y) (hx : WNF x) : WNF y := by
  induction h with
  | refl => exact hx
  | step _ ih => exact ih.psi.piF

theorem Ch.le {x y : Tm} (h : Ch x y) (hx : WNF x) : Le x y := by
  induction h with
  | refl => exact Or.inl rfl
  | step h' ih =>
    have w := h'.wnf hx
    exact le_transY hx w w.psi.piF ih (Or.inr (lt_psi_targetY w))

theorem not_tgt_psi {π b : Tm} : ¬ IsTgt (.Psi π b) := by
  rintro (e | ⟨c, e, -⟩ | ⟨n, p, e⟩) <;> cases e

/-- 崩壊先でない項に至る列は長さ 0 -/
theorem Ch.eq_of_not_tgt {x y : Tm} (h : Ch x y) (hx : WNF x) (hy : ¬ IsTgt y) : x = y := by
  cases h with
  | refl => rfl
  | step h' => exact absurd (h'.wnf hx).psi.tgt hy

/-- 列の行き着く先が `η` の崩壊になるときの仮定 -/
def H15 (η : Tm) : Prop := ∀ γ τ, Good γ → Lt γ η → (∀ δ, Wmax δ → Le γ δ → Wmax γ) →
  IsColl η τ → Ch γ τ → Hull γ Wmax τ → (∀ w, w ∈ fr τ τ → Lt w γ) → Wmax γ

theorem fr_self_psi (π a : Tm) : fr (.Psi π a) (.Psi π a) = fr (.Psi π a) π ++ fr (.Psi π a) a := by
  rw [fr]; simp [Lt.irrefl]

/-- `η` 未満の `Good` な崩壊 `γ` から崩壊先をたどる -/
theorem chain_walk {η γ : Tm} (hG : Good η) (h15 : H15 η) (hγ : Good γ) (hγη : Lt γ η)
    (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) :
    ∀ τ, Ch γ τ → Hull γ Wmax τ → Lt τ η → (∀ w, w ∈ fr τ τ → Lt w γ) →
      (τ = γ ∨ IsTgt τ) → ((∃ n b, τ = .Xi n b) ∨ ∃ ρ a, τ = .Psi ρ a) → Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  intro τ
  induction τ using size_induction with
  | h τ ih =>
  intro hch hτH hτη hfr hτt hsh
  have wτ := hch.wnf wγ
  have hγτ := hch.le wγ
  have fin : Hull η Wmax τ → Wmax γ := fun h => Obs τ (hG.2 τ h hτη) hγτ
  rcases hsh with ⟨n, b, rfl⟩ | ⟨ρ, a, rfl⟩
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | xi hw hγK hb =>
      have wK := WNF.M' hw.xi.1
      have hτK : Lt (.Xi n b) (.M n) := (lt_M_iffY hw hw.xi.1).mpr (Nat.le_refl _)
      rcases triY wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.M hw.xi.1) hKη) (le_transY wγ hw wK hγτ (Or.inr hτK))
      · exact h15 γ _ hγ hγη Obs (Or.inl ⟨n, b, e.symm, rfl⟩) hch (Hull.xi hw hγK hb) hfr
      · apply fin
        refine Hull.xi hw hηK (hull_transfer wη wK (Or.inr hηK) (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) ?_)
        intro w hw'
        apply hfr w
        rw [fr_self_xi]
        exact fr_subY wK hw (Or.inr hτK) hw.xi.2.1 hw' (k2xY hw w hw')
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | psi hw hγρ hρ ha =>
      have wρ := hw.psi.piF
      have hτρ : Le (.Psi ρ a) ρ := Or.inr (lt_psi_targetY hw)
      have frp : ∀ w, w ∈ fr ρ ρ → Lt w γ := by
        intro w h
        have h1 := fr_subY wρ hw hτρ wρ h (k2tY hw w h)
        apply hfr w
        rw [fr_self_psi]
        exact List.mem_append_left _ h1
      have fra : ∀ w, w ∈ fr ρ a → Lt w γ := by
        intro w h
        have h1 := fr_subY wρ hw hτρ hw.psi.aF h (k2Y hw w h)
        apply hfr w
        rw [fr_self_psi]
        exact List.mem_append_right _ h1
      rcases triY wρ wη with hρη | e | hηρ
      · rcases hw.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
        · -- `Ω_0`
          exact Obs _ (hG.2 _ (Hull.om wρ Hull.zero) hρη) (le_transY wγ hw wρ hγτ hτρ)
        · -- `Ω_c`：`τ = γ`
          have hτγ : Tm.Psi (.Om c) a = γ := by
            rcases hτt with e | ht
            · exact e
            · exact absurd ht not_tgt_psi
          have hc : Wmax c := by
            cases hρ with
            | mem hX _ _ => exact wmax_om_arg hX
            | om _ hc => exact hγ.2 c hc (by rw [← hτγ]; exact cxY hw hs)
          exact Obs _ (hG.2 _ (Hull.om wρ (wmax_hull hc wη)) hρη) (le_transY wγ hw wρ hγτ hτρ)
        · exact ih _ (by size_omega) (Ch.step hch) hρ hρη frp
            (Or.inr (Or.inr (Or.inr ⟨n, p, rfl⟩))) (Or.inl ⟨n, p, rfl⟩)
      · exact h15 γ _ hγ hγη Obs (Or.inr ⟨a, by rw [e]⟩) hch (Hull.psi hw hγρ hρ ha) hfr
      · exact fin (Hull.psi hw hηρ
          (hull_transfer wη wρ (Or.inr hηρ) (ρ.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            ρ hρ (Nat.lt_succ_self _) frp)
          (hull_transfer wη wρ (Or.inr hηρ) (a.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            a ha (Nat.lt_succ_self _) fra))

/-- 段階 3：`η` 未満の `Good` な項は `Wmax` に入る -/
theorem step_three {η γ : Tm} (hG : Good η) (h15 : H15 η)
    (hγ : Good γ) (hγη : Lt γ η) (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) : Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  have frγ : ∀ w, w ∈ fr γ γ → Lt w γ := fun w h => (fr_spec h).2
  cases γ with
  | zero => exact hG.2 _ Hull.zero hγη
  | M n => exact hG.2 _ (Hull.M wγ.M) hγη
  | plus g₁ g₂ =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw hg₁ hg₂ =>
      exact hG.2 _ (Hull.plus hw (wmax_hull (hγ.2 _ hg₁ (lt_plus_leftY hw)) wη)
        (wmax_hull (hγ.2 _ hg₂ (lt_plus_rightY hw)) wη)) hγη
  | Om e =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | om hw he => exact hG.2 _ (Hull.om hw (wmax_hull (hγ.2 e he (lt_om_selfY hw)) wη)) hγη
  | Xi n b =>
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inl ⟨n, b, rfl⟩)
  | Psi ρ a =>
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inr ⟨ρ, a, rfl⟩)

/-- `H15 η` の下で `Good η` から拡張の仮定が成り立つ -/
theorem hyp_of_good {η : Tm} (hG : Good η) (h15 : H15 η) : Hyp η := by
  have wη := hG.1.wf_of
  intro β wβ hle γ hW hγ
  have hnβ := nr_specY β wβ
  have key : ∀ γ, Acc (Rel (Hull β Wmax)) γ → Hull β Wmax γ → Lt γ (nrY β) → Wmax γ := by
    intro γ hacc
    induction hacc with
    | intro γ hacc' MIH0 =>
      intro hγH hγ
      have wγ := hγH.wf_of
      have MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_transY hζ.wf_of wγ hnβ.1 hζγ hγ)
      have Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        by_cases hδβ : Lt δ β
        · exact wmax_bounded wδ (Hull.lower HW wδ wβ (Or.inr hδβ) hγH) hδ hγδ
            (nr_specY δ wδ).2.2
        · exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_ltY wδ wβ hδβ⟩ γ).mp
            ⟨⟨hγH, Acc.intro γ hacc'⟩, hγ⟩).1
      have G2 : ∀ α, Hull γ Wmax α → Lt α γ → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          by_cases hβnγ : Lt β (nrY γ)
          · exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          · have below : ∀ x, WNF x → Lt x α → Lt x γ :=
              fun x wx h => lt_transY wx hα.wf_of wγ h hαγ
            cases hα with
            | zero => exact MIH _ Hull.zero hαγ
            | M hn => exact MIH _ (Hull.M hn) hαγ
            | mem hX _ _ => exact hX
            | plus hw ha hb =>
              exact MIH _ (Hull.plus hw
                (wmax_hull (ihα _ (by size_omega) ha (below _ hw.plus.1 (lt_plus_leftY hw))) wβ)
                (wmax_hull (ihα _ (by size_omega) hb
                  (below _ hw.plus.2.1 (lt_plus_rightY hw))) wβ)) hαγ
            | om hw ha =>
              exact MIH _ (Hull.om hw (wmax_hull (ihα _ (by size_omega) ha
                (below _ hw.om.1 (lt_om_selfY hw))) wβ)) hαγ
            | @xi n a hw hγK ha =>
              have wK := WNF.M' hw.xi.1
              by_cases hβK : Lt β (.M n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK (Or.inr hβK) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (k2xY hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltY wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi π a hw hγσ hσ ha =>
              have wπ := hw.psi.piF
              by_cases hβσ : Lt β π
              · have hσ' := hull_transfer wβ wπ (Or.inr hβσ) _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  π hσ (by size_omega)
                  (fun w hw' => lt_transY (wπ.of_mem_subs (fr_spec hw').1) hw wγ
                    (k2tY hw w hw') hαγ)
                exact MIH _ (Hull.psi hw hβσ hσ' (hull_transfer wβ wπ (Or.inr hβσ) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (k2Y hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨π, a, rfl, hγσ, le_of_not_ltY wβ wπ hβσ⟩)
                  (Hull.psi hw hγσ hσ ha) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_leY wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

/-! ### `H15` は常に成り立つ -/

/-- 崩壊先でも `M_n` でもない項 -/
theorem h15_nt {η : Tm} (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .M n) : H15 η := by
  intro γ τ hγ _ _ hc hch _ _
  have wτ := hch.wnf hγ.1.wf_of
  rcases hc with ⟨n, b, e, -⟩ | ⟨b, rfl⟩
  · exact absurd e (hK n)
  · exact absurd wτ.psi.tgt hT

theorem wmax_of_good_nt {η : Tm} (hG : Good η) (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .M n) :
    Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (h15_nt hT hK))

/-- `M_n` でない項：崩壊 `Ψ_η(b)` は崩壊先にならない -/
theorem h15_notM {η : Tm} (hK : ∀ n, η ≠ .M n) : H15 η := by
  intro γ τ hγ _ _ hc hch _ _
  have wγ := hγ.1.wf_of
  rcases hc with ⟨n, b, e, -⟩ | ⟨b, rfl⟩
  · exact absurd e (hK n)
  · have e := hch.eq_of_not_tgt wγ not_tgt_psi
    subst e
    exact wmax_of_good_nt hγ not_tgt_psi (fun _ e => by cases e)

theorem wmax_of_good_notM {η : Tm} (hG : Good η) (hK : ∀ n, η ≠ .M n) : Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (h15_notM hK))

theorem h15_M (n : Nat) : H15 (.M n) := by
  intro γ τ hγ _ _ hc hch _ _
  have wγ := hγ.1.wf_of
  rcases hc with ⟨m, b, e, rfl⟩ | ⟨b, rfl⟩
  · cases hch with
    | refl => exact wmax_of_good_notM hγ (fun _ e => by cases e)
    | step h' =>
      have e := h'.eq_of_not_tgt wγ not_tgt_psi
      subst e
      exact wmax_of_good_notM hγ (fun _ e => by cases e)
  · exfalso
    have := (hch.wnf wγ).psi.tgt
    rcases this with e | ⟨c, e, -⟩ | ⟨k, p, e⟩ <;> cases e

/-- `Good` な項は `Wmax` に入る -/
theorem wmax_of_good {η : Tm} (hG : Good η) : Wmax η := by
  cases η with
  | M n => exact wmax_of_good_hyp hG (hyp_of_good hG (h15_M n))
  | _ => exact wmax_of_good_notM hG (fun _ e => by cases e)

end MahloOCF

/-! ## `Wmax` の閉包 -/

namespace MahloOCF

open Tm

theorem wmax_zero : Wmax .zero :=
  wmax_of_good ⟨Hull.zero, fun _ _ h => absurd h (not_lt_zero _)⟩

theorem wmax_add {a b : Tm} (hw : WNF (.plus a b)) (ha : Wmax a) (hb : Wmax b) :
    Wmax (.plus a b) := by
  induction wmax_acc hb with
  | intro b _ ih =>
    have hn := nr_specY _ hw
    have hap := hw.plus.2.2.1
    have ha_lt := lt_transY (wmax_wf ha) hw hn.1 (lt_plus_leftY hw) hn.2.2
    refine wmax_of_good ⟨Hull.plus hw (wmax_hull ha hw) (wmax_hull hb hw), ?_⟩
    intro γ hγ hγlt
    have wγ := hγ.wf_of
    cases γ with
    | zero => exact wmax_zero
    | plus γ₁ γ₂ =>
      by_cases e : γ₁ = a
      · subst e
        have hγlt' := lt_plus_plus_same.mp hγlt
        cases hγ with
        | mem hX _ _ => exact hX
        | plus hw' _ hγ₂ =>
          have hγ₂W := wmax_bounded hw hγ₂ hb (Or.inr hγlt')
            (lt_transY (wmax_wf hb) hw hn.1 (lt_plus_rightY hw) hn.2.2)
          exact ih γ₂ ⟨hγ₂W, hγlt'⟩ hw' hγ₂W
      · exact wmax_bounded hw hγ ha
          (Or.inr ((lt_plus_prin_iffY wγ hap).mpr ((lt_plus_plus_neY wγ hw e).mp hγlt))) ha_lt
    | _ => exact wmax_bounded hw hγ ha ((lt_prin_plus_iffY wγ rfl hw).mp hγlt) ha_lt

theorem wmax_om : ∀ c, Wmax c → WNF (.Om c) → Wmax (.Om c) := by
  intro c hc
  induction wmax_acc hc with
  | intro c _ ihc =>
    intro hw
    have hn := nr_specY _ hw
    have wc := wmax_wf hc
    have hc_lt := lt_transY wc hw hn.1 (lt_om_selfY hw) hn.2.2
    refine wmax_of_good ⟨Hull.om hw (wmax_hull hc hw), ?_⟩
    intro β
    induction β using size_induction with
    | h β ihβ =>
      intro hβ hβlt
      have below : ∀ x, WNF x → Lt x β → Lt x (.Om c) :=
        fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
      cases hβ with
      | zero => exact wmax_zero
      | M hn' =>
        exact wmax_bounded hw (Hull.M hn') hc (Or.inr ((lt_M_omY hn' hw).mp hβlt)) hc_lt
      | mem hX _ _ => exact hX
      | plus hw' hb₁ hb₂ =>
        exact wmax_add hw'
          (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
          (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
      | om hw' hd =>
        have hdW := ihβ _ (by size_omega) hd (below _ hw'.om.1 (lt_om_selfY hw'))
        exact ihc _ ⟨hdW, lt_om_iffG.mp hβlt⟩ hdW hw'
      | @xi n d hw' hK hd =>
        exact wmax_bounded hw (Hull.xi hw' hK hd) hc
          (Or.inr ((lt_OF_omY (Or.inl ⟨n, d, rfl⟩) hw' wc).mp hβlt)) hc_lt
      | @psi π d hw' hσ hπ hd =>
        rcases hw'.psi_shape with rfl | ⟨c', rfl, -⟩ | ⟨n, p, rfl⟩
        · exact absurd (lt_om_iffG.mp hσ) (not_lt_zero c)
        · exact absurd (lt_om_iffG.mp hσ)
            (not_lt_of_leY hw'.psi.piF.om.1 wc ((lt_psiOm_omY hw' wc).mp hβlt))
        · exact wmax_bounded hw (Hull.psi hw' hσ hπ hd) hc
            (Or.inr ((lt_OF_omY (Or.inr ⟨n, p, d, rfl⟩) hw' wc).mp hβlt)) hc_lt

/-- `M_n` 未満の `C^{M_n}(Wmax)` の元は `Wmax` に入る（`M_j`（`j < n`）が `Wmax` に入るとき） -/
theorem goodM {n : Nat} (hn : 1 ≤ n) (ihK : ∀ j, 1 ≤ j → j < n → Wmax (.M j)) :
    Good (.M n) := by
  have hw := WNF.M' hn
  refine ⟨Hull.M hn, ?_⟩
  intro β
  induction β using size_induction with
  | h β ihβ =>
    intro hβ hβlt
    have below : ∀ x, WNF x → Lt x β → Lt x (.M n) :=
      fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
    cases hβ with
    | zero => exact wmax_zero
    | @M j hj =>
      have h1 := (lt_M_iffY (WNF.M' hj) hn).mp hβlt
      simp only [lev] at h1
      exact ihK j hj (by omega)
    | mem hX _ _ => exact hX
    | plus hw' hb₁ hb₂ =>
      exact wmax_add hw'
        (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
        (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
    | om hw' hd =>
      exact wmax_om _ (ihβ _ (by size_omega) hd (below _ hw'.om.1 (lt_om_selfY hw'))) hw'
    | xi hw' hK _ =>
      exfalso
      have h1 := (lt_M_iffY hw' hn).mp hβlt
      have h2 := (lt_M_iffY hw hw'.xi.1).mp hK
      simp only [lev] at h1 h2
      omega
    | psi hw' hσ _ _ =>
      exfalso
      have h1 := (lt_M_iffY hw' hn).mp hβlt
      have h2 := lev_le_of_lt_gen hσ
      simp only [lev] at h1 h2
      omega

theorem wmax_M : ∀ n, 1 ≤ n → Wmax (.M n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro hn
    exact wmax_of_good (goodM hn (fun j hj hjn => ihn j hjn hj))

end MahloOCF

/-! ## `M_n^+` 以下の範囲 `WK n` -/

namespace MahloOCF

open Tm

theorem succM_eq (n : Nat) : succM n = .Om (succT (.M n)) := rfl

theorem WNF.succM {n : Nat} (hn : 1 ≤ n) : WNF (succM n) := WNF.om_succT (WNF.M' hn)

theorem nrY_M_eq (n : Nat) : nrY (.M n) = succM n := rfl

theorem M_lt_succM {n : Nat} (hn : 1 ≤ n) : Lt (.M n) (succM n) :=
  (nr_specY _ (WNF.M' hn)).2.2

/-- `M_n^+` 以下の `C^{M_n}(Wmax)` の元で、`M_n` 以上の節点の引数が `M_n^+` 未満のもの -/
def WK (n : Nat) (x : Tm) : Prop :=
  Hull (.M n) Wmax x ∧ inC x (succM n) (.M n) = true ∧ Le x (succM n)

theorem WK.wf {n : Nat} {x : Tm} (h : WK n x) : WNF x := h.1.wf_of

/-- `x < d` なら `x ∈ C(g, d)` -/
theorem inC_of_ltY : ∀ {x : Tm} (g : Tm) {d : Tm}, WNF x → WNF d → Lt x d → inC x g d = true
  | .zero, _, _, _, _, _ => inC_zero _ _
  | .M _, _, _, _, _, _ => inC_M _ _ _
  | .plus a b, g, d, hx, hd, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, inC_of_ltY g ha hd (lt_transY ha hx hd (lt_plus_leftY hx) h),
      inC_of_ltY g hb hd (lt_transY hb hx hd (lt_plus_rightY hx) h)]
    rfl
  | .Om a, g, d, hx, hd, h => by
    rw [inC_om]
    exact inC_of_ltY g hx.om.1 hd (lt_transY hx.om.1 hx hd (lt_om_selfY hx) h)
  | .Xi m a, _, _, _, _, h => inC_of_lt_node (Or.inl ⟨m, a, rfl⟩) h
  | .Psi p a, _, _, _, _, h => inC_of_lt_node (Or.inr ⟨p, a, rfl⟩) h

theorem inC_mono_g {x g g' d : Tm} (hx : WNF x) (hg : WNF g) (hg' : WNF g') (hle : Le g g')
    (h : inC x g d = true) : inC x g' d = true :=
  inC_mono x g d g' d h (fun _ _ h => h)
    (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg hg' hvg hle)

theorem hull_plus_inv {α a b : Tm} (wα : WNF α) (h : Hull α Wmax (.plus a b)) :
    Hull α Wmax a ∧ Hull α Wmax b := by
  cases h with
  | mem hX _ _ =>
    have hG := wmax_good hX
    cases hG.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw' ha hb =>
      exact ⟨wmax_hull (hG.2 _ ha (lt_plus_leftY hw')) wα,
        wmax_hull (hG.2 _ hb (lt_plus_rightY hw')) wα⟩
  | plus _ ha hb => exact ⟨ha, hb⟩

theorem WK.plus {n : Nat} (hn : 1 ≤ n) {a b : Tm} (h : WK n (.plus a b)) : WK n a ∧ WK n b := by
  have wx := h.wf
  have wS := WNF.succM hn
  obtain ⟨ha, hb⟩ := hull_plus_inv (WNF.M' hn) h.1
  have hC := h.2.1
  rw [inC_plus, Bool.and_eq_true] at hC
  exact ⟨⟨ha, hC.1, Or.inr (lt_of_lt_of_leY wx.plus.1 wx wS (lt_plus_leftY wx) h.2.2)⟩,
    ⟨hb, hC.2, Or.inr (lt_of_lt_of_leY wx.plus.2.1 wx wS (lt_plus_rightY wx) h.2.2)⟩⟩

theorem WK.psi_arg {n : Nat} {κ d : Tm} (h : WK n (.Psi κ d))
    (hK : ¬ Lt (.Psi κ d) (.M n)) : WK n d ∧ Lt d (succM n) := by
  have hd : Hull (.M n) Wmax d := by
    cases h.1 with
    | mem _ _ hlt => exact absurd hlt hK
    | psi _ _ _ hd => exact hd
  rcases inC_psi_iff.mp h.2.1 with h' | ⟨-, hdC, hdS⟩
  · exact absurd h' hK
  · exact ⟨⟨hd, hdC, Or.inr hdS⟩, hdS⟩

/-! ### `M_n^+` 未満の項の形 -/

theorem om_lt_succM {n : Nat} (hn : 1 ≤ n) {c : Tm} (hw : WNF (.Om c))
    (h : Lt (.Om c) (succM n)) : Lt (.Om c) (.M n) := by
  have wc := hw.om.1
  have wK := WNF.M' hn
  have wS := succT_WNF wK
  have hc : Lt c (succT (.M n)) := lt_om_iffG.mp h
  have hcK : Lt c (.M n) := by
    rcases triY wc wK with h' | e | h'
    · exact h'
    · subst e; exact absurd hw not_WNF_om_M
    · exact absurd hc (not_lt_of_leY wS wc (succT_leY wK wc h'))
  rw [lt_M_iffY hw hn]
  have := (lt_M_iffY wc hn).mp hcK
  simp only [lev]
  omega

theorem M_lt_of_lev {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : WNF x) (hl : lev x = n + 1)
    (hne : x ≠ .M n) : Lt (.M n) x := by
  rcases triY (WNF.M' hn) hx with h | e | h
  · exact h
  · exact absurd e.symm hne
  · have := (lt_M_iffY hx hn).mp h; omega

theorem lev_succM (n : Nat) : lev (succM n) = n + 1 := by
  simp only [succM, lev]; omega

theorem xi_le_succM {n m : Nat} (hn : 1 ≤ n) {d : Tm} (hw : WNF (.Xi m d))
    (h : Le (.Xi m d) (succM n)) : Lt (.Xi m d) (.M n) := by
  have wS := WNF.succM hn
  have hl : m ≤ n + 1 := by
    rcases h with e | h
    · cases e
    · have := lev_le_of_lt_gen h; rw [lev_succM] at this; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact (lt_M_iffY hw hn).mpr (by simp only [lev]; omega)
  · exfalso
    subst hl
    have h1 : Lt (.M n) (.Xi (n + 1) d) := M_lt_of_lev hn hw rfl (fun e => by cases e)
    have h2 : Lt (succT (.M n)) (.Xi (n + 1) d) :=
      (lt_plus_prin_iffY (succT_WNF (WNF.M' hn)) rfl).mpr h1
    have h3 : Lt (succM n) (.Xi (n + 1) d) :=
      (lt_om_OFG (Or.inl ⟨n + 1, d, rfl⟩) hw).mpr h2
    exact not_lt_of_leY hw wS h h3

theorem M_le_succM {n m : Nat} (h : Le (.M m) (succM n)) : m ≤ n := by
  rcases h with e | h
  · cases e
  · have := lev_le_of_lt_gen h; rw [lev_succM] at this; simp only [lev] at this; omega

/-- `M_n ≤ Ψ_κ(d) < M_n^+` なら `κ = M_n^+` -/
theorem psi_lt_succM {n : Nat} (hn : 1 ≤ n) {κ d : Tm} (hw : WNF (.Psi κ d))
    (h : Lt (.Psi κ d) (succM n)) (hK : ¬ Lt (.Psi κ d) (.M n)) : κ = succM n := by
  have wK := WNF.M' hn
  have wS1 := succT_WNF wK
  have hl1 : lev κ ≤ n + 1 := by
    have := lev_le_of_lt_gen h; rw [lev_succM] at this; simpa [lev] using this
  have hl2 : n + 1 ≤ lev κ := by
    apply Nat.le_of_not_lt
    intro hc
    exact hK ((lt_M_iffY hw hn).mpr (by simp only [lev]; omega))
  rcases hw.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨m, p, rfl⟩
  · simp only [lev] at hl2; omega
  · have wc := hw.psi.piF.om.1
    have hcS : Le c (succT (.M n)) := (lt_psiOm_omY hw wS1).mp h
    have hlc : lev c = n + 1 := by simp only [lev] at hl1 hl2; omega
    have hKc : Lt (.M n) c := by
      rcases triY wK wc with h' | e | h'
      · exact h'
      · subst e; simp [isSucc, summands, one] at hs
      · have := (lt_M_iffY wc hn).mp h'; omega
    have := le_antisymmY wc wS1 hcS (succT_leY wK wc hKc)
    subst this
    rfl
  · exfalso
    have hO : IsOF (.Psi (.Xi m p) d) := Or.inr ⟨m, p, d, rfl⟩
    have h1 : Lt (.Psi (.Xi m p) d) (succT (.M n)) := (lt_OF_omY hO hw wS1).mp h
    rcases (lt_prin_plus_iffY hw rfl wS1).mp h1 with e | h2
    · cases e
    · exact hK h2

/-! ### `WK n` の整礎性 -/

theorem acc_wk_of_wmax {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : Wmax x) (h : Lt x (succM n)) :
    Acc (Rel (WK n)) x :=
  acc_of_below (fun _ h => h.wf) x (wmax_acc hx) (wmax_wf hx)
    (fun _ hy hyx => wmax_bounded (WNF.M' hn) hy.1 hx (Or.inr hyx) (by rw [nrY_M_eq]; exact h))

theorem acc_wk_of_ltK {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) {x : Tm} (hx : WK n x)
    (h : Lt x (.M n)) : Acc (Rel (WK n)) x :=
  acc_wk_of_wmax hn (hG.2 x hx.1 h)
    (lt_transY hx.wf (WNF.M' hn) (WNF.succM hn) h (M_lt_succM hn))

theorem acc_wk_K {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) : Acc (Rel (WK n)) (.M n) :=
  Acc.intro _ (fun _ hy => acc_wk_of_ltK hn hG hy.1 hy.2)

theorem acc_wk_plus {n : Nat} (hn : 1 ≤ n) : ∀ v, Acc (Rel (WK n)) v → ∀ u,
    Acc (Rel (WK n)) u → WNF (.plus u v) → Acc (Rel (WK n)) (.plus u v) := by
  intro v hacc
  induction hacc with
  | intro v _ ih =>
    intro u hu hw
    have hup := hw.plus.2.2.1
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    have wy := hy.wf
    cases y with
    | zero => exact Acc.intro _ (fun z hz => absurd hz.2 (not_lt_zero _))
    | plus y₁ y₂ =>
      by_cases e : y₁ = u
      · subst e
        exact ih y₂ ⟨(hy.plus hn).2, lt_plus_plus_same.mp hyl⟩ y₁ hu wy
      · exact hu.inv ⟨hy, (lt_plus_prin_iffY wy hup).mpr ((lt_plus_plus_neY wy hw e).mp hyl)⟩
    | _ =>
      rcases (lt_prin_plus_iffY wy rfl hw).mp hyl with e | h
      · rw [e]; exact hu
      · exact hu.inv ⟨hy, h⟩

/-- `M_n^+` を崩壊先とする崩壊：`d ∈ WK n` が整礎なら `Ψ_{M_n^+}(d)` も -/
theorem acc_psiM {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) :
    ∀ d, Acc (Rel (WK n)) d → WK n d → Lt d (succM n) → WNF (.Psi (succM n) d) →
      Acc (Rel (WK n)) (.Psi (succM n) d) := by
  have wS := WNF.succM hn
  intro d hacc
  induction hacc with
  | intro d hd' ihd =>
    intro hd hdS hw
    have hψS : Lt (.Psi (succM n) d) (succM n) := lt_psi_targetY hw
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    revert hy hyl
    induction y using size_induction with
    | h y ihy =>
    intro hy hyl
    have wy := hy.wf
    by_cases hyK : Lt y (.M n)
    · exact acc_wk_of_ltK hn hG hy hyK
    have hyS : Lt y (succM n) := lt_transY wy hw wS hyl hψS
    cases y with
    | zero => exact absurd ((lt_M_iffY wy hn).mpr (by simp [lev])) hyK
    | M m =>
      have hm := M_le_succM (Or.inr hyS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_M_iffY wy hn).mpr (by simp only [lev]; omega)) hyK
      · exact acc_wk_K hn hG
    | plus y₁ y₂ =>
      have h12 := hy.plus hn
      have h1 : Lt y₁ (.Psi (succM n) d) := (lt_plus_prin_iffY wy rfl).mp hyl
      have h2 : Lt y₂ (.Psi (succM n) d) :=
        lt_transY wy.plus.2.1 wy hw (lt_plus_rightY wy) hyl
      exact acc_wk_plus hn y₂ (ihy y₂ (by size_omega) h12.2 h2) y₁
        (ihy y₁ (by size_omega) h12.1 h1) wy
    | Om c => exact absurd (om_lt_succM hn wy hyS) hyK
    | Xi m e => exact absurd (xi_le_succM hn wy (Or.inr hyS)) hyK
    | Psi κ e =>
      have hκ := psi_lt_succM hn wy hyS hyK
      subst hκ
      obtain ⟨he, heS⟩ := hy.psi_arg hyK
      exact ihd e ⟨he, lt_psi_psi_same.mp hyl⟩ he heS wy

/-- `WK n` は整礎 -/
theorem acc_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) :
    ∀ x, WK n x → Acc (Rel (WK n)) x := by
  have key : ∀ x, WK n x → Lt x (succM n) → Acc (Rel (WK n)) x := by
    intro x
    induction x using size_induction with
    | h x ih =>
    intro hx hxS
    have wx := hx.wf
    by_cases hxK : Lt x (.M n)
    · exact acc_wk_of_ltK hn hG hx hxK
    cases x with
    | zero => exact absurd ((lt_M_iffY wx hn).mpr (by simp [lev])) hxK
    | M m =>
      have hm := M_le_succM (Or.inr hxS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_M_iffY wx hn).mpr (by simp only [lev]; omega)) hxK
      · exact acc_wk_K hn hG
    | plus a b =>
      have hab := hx.plus hn
      have wS := WNF.succM hn
      exact acc_wk_plus hn b (ih b (by size_omega) hab.2
          (lt_transY wx.plus.2.1 wx wS (lt_plus_rightY wx) hxS)) a
        (ih a (by size_omega) hab.1 (lt_transY wx.plus.1 wx wS (lt_plus_leftY wx) hxS)) wx
    | Om c => exact absurd (om_lt_succM hn wx hxS) hxK
    | Xi m e => exact absurd (xi_le_succM hn wx (Or.inr hxS)) hxK
    | Psi κ e =>
      have hκ := psi_lt_succM hn wx hxS hxK
      subst hκ
      obtain ⟨he, heS⟩ := hx.psi_arg hxK
      exact acc_psiM hn hG e (ih e (by size_omega) he heS) he heS wx
  intro x hx
  rcases hx.2.2 with e | h
  · subst e
    exact Acc.intro _ (fun y hy => key y hy.1 hy.2)
  · exact key x hx h

end MahloOCF

/-! ## `Ξ_n`・`Ψ_π` の閉包と整列性 -/

namespace MahloOCF

open Tm

theorem succM_mono {j n : Nat} (h : j ≤ n) : Le (succM j) (succM n) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inr (lt_of_lev_lt' (by rw [lev_succM, lev_succM]; omega))
  · exact Or.inl rfl

/-- `b` を引数とする崩壊が `Wmax` に入る（階 `n` 以下） -/
def CollOK (n : Nat) (b : Tm) : Prop :=
  (∀ j, 1 ≤ j → j ≤ n → WNF (.Xi j b) → Wmax (.Xi j b)) ∧
    (∀ π, Wmax π → Lt π (.M n) → WNF (.Psi π b) → Wmax (.Psi π b))

/-- 係数についての帰納法で使う性質 -/
def PK (n : Nat) (x : Tm) : Prop :=
  Hull (.M n) Wmax x ∧ (Le x (succM n) → inC x (succM n) (.M n) = true)

/-- `C^{M_n}(Wmax)` の元の前線（`M_n` 以下の `R` について）は `Wmax` に入る -/
theorem fr_hullK {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) {x R : Tm}
    (hx : Hull (.M n) Wmax x) (wR : WNF R) (hR : Le R (.M n)) :
    ∀ w, w ∈ fr R x → Wmax w := by
  intro w hw
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) x hx w hw with h | h
  · exact h
  · exact hG.2 w h (lt_of_lt_of_leY (hx.wf_of.of_mem_subs (fr_spec hw).1) wR (WNF.M' hn)
      (fr_spec hw).2 hR)

/-- `Ξ_j(d)` の引数は `M_n^+` 以下（`j ≤ n`） -/
theorem xi_arg_le {j n : Nat} {d : Tm} (hw : WNF (.Xi j d)) (hjn : j ≤ n) : Le d (succM n) :=
  le_transY hw.xi.2.1 (WNF.succM hw.xi.1) (WNF.succM (Nat.le_trans hw.xi.1 hjn))
    (le_of_ne_gtY hw.xi.2.1 (WNF.succM hw.xi.1) hw.xi.2.2.1) (succM_mono hjn)

/-- 係数についての帰納法（引数 `a` 未満の引数の崩壊が `Wmax` に入るとき） -/
theorem coeffK {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) {θ R g : Tm} (wθ : WNF θ) (hθK : Lt θ (.M n))
    (wg : WNF g) (hga : Le g a) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      PK n x := by
  have wK := WNF.M' hn
  have wS := WNF.succM hn
  have wa := ha.wf
  have hgS : ∀ {d}, WNF d → Lt d g → Lt d (succM n) := fun wd h =>
    lt_of_lt_of_leY wd wg wS h (le_transY wg wa wS hga ha.2.2)
  refine coeff_induction (PK n) S
    (fun x hx hxθ hs => ⟨wmax_hull (good x hx hxθ hs) wK,
      fun _ => inC_of_ltY _ hx.wf_of wK (lt_transY hx.wf_of wθ wK hxθ hθK)⟩)
    ⟨Hull.zero, fun _ => inC_zero _ _⟩
    (fun hj => ⟨Hull.M hj, fun _ => inC_M _ _ _⟩) ?_ ?_ ?_ ?_
  · intro a' b' hw h1 h2
    refine ⟨Hull.plus hw h1.1 h2.1, fun hle => ?_⟩
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨h1.2 (Or.inr (lt_of_lt_of_leY hw.plus.1 hw wS (lt_plus_leftY hw) hle)),
      h2.2 (Or.inr (lt_of_lt_of_leY hw.plus.2.1 hw wS (lt_plus_rightY hw) hle))⟩
  · intro a' hw h1
    refine ⟨Hull.om hw h1.1, fun hle => ?_⟩
    rw [inC_om]
    exact h1.2 (Or.inr (lt_of_lt_of_leY hw.om.1 hw wS (lt_om_selfY hw) hle))
  · intro j d hw hdg hd
    have wd := hw.xi.2.1
    have hj := hw.xi.1
    by_cases hjn : j ≤ n
    · have hnode : Lt (.Xi j d) (.M n) := (lt_M_iffY hw hn).mpr hjn
      have hdS : Le d (succM n) := xi_arg_le hw hjn
      have hW : Wmax (.Xi j d) :=
        (MIH d ⟨hd.1, hd.2 hdS, hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).1 j hj hjn hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKj : Lt (.M n) (.M j) := lt_of_lev_lt' (by simp only [lev]; omega)
      refine ⟨Hull.xi hw hKj hd.1, fun hle => ?_⟩
      have := (lt_M_iffY hw hn).mp (xi_le_succM hn hw hle)
      simp only [lev] at this
      exact absurd this hjn
  · intro κ d hw hdg hκ hd
    have hP := hw.psi
    have wd := hP.aF
    have hdS : Lt d (succM n) := hgS wd hdg
    by_cases hnode : Lt (.Psi κ d) (.M n)
    · have hκK : Lt κ (.M n) := (lt_M_iffY hP.piF hn).mpr ((lt_M_iffY hw hn).mp hnode)
      have hW : Wmax (.Psi κ d) :=
        (MIH d ⟨hd.1, hd.2 (Or.inr hdS), Or.inr hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).2 κ
          (hG.2 κ hκ.1 hκK) hκK hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKκ : Lt (.M n) κ :=
        lt_of_le_of_ltY wK hw hP.piF (le_of_not_ltY hw wK hnode) (lt_psi_targetY hw)
      refine ⟨Hull.psi hw hKκ hκ.1 hd.1, fun hle => ?_⟩
      have hlt : Lt (.Psi κ d) (succM n) := by
        rcases hle with e | h
        · cases e
        · exact h
      have hκS := psi_lt_succM hn hw hlt hnode
      subst hκS
      exact inC_psi_iff.mpr (Or.inr ⟨hκ.2 (Or.inl rfl), hd.2 (Or.inr hdS), hdS⟩)

/-- `WK n` の元を引数とする階 `n` 以下の崩壊は `Wmax` に入る（引数 `a ∈ WK n` についての帰納法） -/
theorem coll_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.M n)) : ∀ a, WK n a → CollOK n a := by
  have wK := WNF.M' hn
  intro a ha
  induction acc_wk hn hG a ha with
  | intro a _ MIH0 =>
    have MIH : ∀ b, WK n b → Lt b a → CollOK n b := fun b hb hba => MIH0 b ⟨hb, hba⟩ hb
    have wa := ha.wf
    have hullK : ∀ {η x}, WNF η → Lt η (.M n) → Hull (.M n) Wmax x → Hull η Wmax x :=
      fun wη hηK hx => Hull.lower HW wη wK (Or.inr hηK) hx
    have wkOf : ∀ {x}, PK n x → Le x (succM n) → WK n x := fun h hle => ⟨h.1, h.2 hle, hle⟩
    refine ⟨fun j hj hjn hw => ?_, fun π hπ hπK hw => ?_⟩
    · -- `Ξ_j(a)`
      have wKj := WNF.M' hj
      have hXK : Lt (.Xi j a) (.M j) := (lt_M_iffY hw hj).mpr (Nat.le_refl _)
      have hXKn : Lt (.Xi j a) (.M n) := (lt_M_iffY hw hn).mpr hjn
      have hnα := nr_specY _ hw
      have bound : ∀ x w, Hull (.Xi j a) Wmax x → Wmax w → Lt w (.Xi j a) → ¬ Lt w x →
          Wmax x := fun x w hx hW hwlt hn' =>
        wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn')
          (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
      have hKjn : Le (.M j) (.M n) := by
        rcases Nat.lt_or_eq_of_le hjn with h | rfl
        · exact Or.inr (lt_of_lev_lt' (by simp only [lev]; omega))
        · exact Or.inl rfl
      refine wmax_of_good ⟨Hull.xi hw hXK (hullK hw hXKn ha.1), ?_⟩
      intro β1
      induction β1 using size_induction with
      | h β1 LIH =>
        intro hβ hβlt
        have below : ∀ x, WNF x → Lt x β1 → Lt x (.Xi j a) :=
          fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
        cases hβ with
        | zero => exact wmax_zero
        | M hj' => exact hG.2 _ (Hull.M hj') (lt_transY (WNF.M' hj') hw wK hβlt hXKn)
        | mem hX _ _ => exact hX
        | plus hw₁ hb₁ hb₂ =>
          exact wmax_add hw₁
            (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
            (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
        | om hw₁ hd =>
          exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 (lt_om_selfY hw₁))) hw₁
        | @xi j' d hw₁ hXKj hd =>
          have hjj : j' = j := by
            have h1 := (lt_M_iffY hw hw₁.xi.1).mp hXKj
            have h2 := lev_le_of_lt_gen hβlt
            simp only [lev] at h1 h2
            omega
          subst hjj
          by_cases hda : d = a
          · subst hda
            exact absurd hβlt (Lt.irrefl _)
          have wd := hw₁.xi.2.1
          rcases (lt_xi_xi0 hda).mp hβlt with ⟨hdlt, hin⟩ | ⟨had, hn'⟩
          · have hfr : ∀ w, w ∈ fr (.M j') d → Lt w (.Xi j' a) := fun w hw' => by
              have hwF := wd.of_mem_subs (fr_spec hw').1
              exact coll_xi0 hw w hwF
                (fr_of_inC d (fun v _ hnv => not_lt_of_not_lt_M (y := Tm.Xi j' a) rfl hnv) hin w hw')
                (fr_spec hw').2
            have hPd := coeffK hn hG ha MIH hw hXKn wd (Or.inr hdlt) _
              (fun x hx hxθ hs => LIH x hs hx hxθ) d hd (by size_omega) hfr hw₁.xi.2.2.2
            exact (MIH d (wkOf hPd (xi_arg_le hw₁ hjn)) hdlt).1 j' hj hjn hw₁
          · obtain ⟨w, hwfr, hwn⟩ := wit_of_not_inC hw.xi.2.2.2
              (fun v hv h => lt_transY (wa.of_mem_subs hv) wa wd h had) hn'
            exact bound _ w (Hull.xi hw₁ hXKj hd)
              (fr_hullK hn hG ha.1 wKj hKjn w hwfr) (k2xY hw w hwfr) hwn
        | @psi κ d hw₁ hσ hκ hd =>
          have hl : lev κ = j := by
            have h1 := lev_le_of_lt_gen hσ
            have h2 := lev_le_of_lt_gen hβlt
            simp only [lev] at h1 h2
            omega
          have hgt : cmp κ (.Xi j a) = .gt := by
            unfold Lt at hσ; rw [swapY hw hw₁.psi.piF, hσ]; rfl
          rcases (lt_psi_xiY hl).mp hβlt with h' | h'
          · exact absurd hgt h'
          · rw [baseOf_xi] at h'
            have hk : (cmp (kTerm (j - 1)) (Tm.Psi κ d) == .lt) = true := by
              have := kTerm_lt (n := j) hj hw₁ rfl rfl hl
              unfold Lt at this; rw [this]; rfl
            rw [hk, Bool.true_and] at h'
            obtain ⟨w, hwfr, hwn⟩ := wit_of_not_inC hw.xi.2.2.2 (fun _ _ h => h) h'
            exact bound _ w (Hull.psi hw₁ hσ hκ hd)
              (fr_hullK hn hG ha.1 wKj hKjn w hwfr) (k2xY hw w hwfr) hwn
    · -- `Ψ_π(a)`
      have wπ := wmax_wf hπ
      have hnα := nr_specY _ hw
      have hγπ := lt_psi_targetY hw
      have hηK : Lt (.Psi π a) (.M n) := lt_transY hw wπ wK hγπ hπK
      have bound : ∀ x w, Hull (.Psi π a) Wmax x → Wmax w → Lt w (.Psi π a) →
          ¬ Lt w x → Wmax x := fun x w hx hW hwlt hn' =>
        wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn')
          (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
      -- 崩壊先 `Ξ_m(δ)` の前線で押さえる
      have viaXi : ∀ {δ x : Tm} {mm : Nat}, π = .Xi mm δ → Hull (.Psi π a) Wmax x → WNF x →
          (∃ w, w ∈ fr (.M mm) δ ∧ ¬ Lt w x) → Wmax x := by
        intro δ x mm e hx wx ⟨w, hwfr, hwn⟩
        subst e
        have wM := WNF.M' wπ.xi.1
        have hwπ := k2xY wπ w hwfr
        have hwπ' : w ∈ fr (.Xi mm δ) (.Xi mm δ) := by
          rw [fr_self_xi]
          exact fr_subY wM wπ (Or.inr ((lt_M_iffY wπ wπ.xi.1).mpr (Nat.le_refl _))) wπ.xi.2.1
            hwfr hwπ
        exact bound x w hx (fr_wmax wπ _ hπ w hwπ') (k2tY hw w hwπ') hwn
      refine wmax_of_good ⟨Hull.psi hw hγπ (wmax_hull hπ hw) (hullK hw hηK ha.1), ?_⟩
      intro β1
      induction β1 using size_induction with
      | h β1 LIH =>
        intro hβ hβlt
        have good : ∀ x, Hull (.Psi π a) Wmax x → Lt x (.Psi π a) →
            x.size < β1.size → Wmax x := fun x hx hxθ hs => LIH x hs hx hxθ
        have below : ∀ x, WNF x → Lt x β1 → Lt x (.Psi π a) :=
          fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
        cases hβ with
        | zero => exact wmax_zero
        | M hj' => exact hG.2 _ (Hull.M hj') (lt_transY (WNF.M' hj') hw wK hβlt hηK)
        | mem hX _ _ => exact hX
        | plus hw₁ hb₁ hb₂ =>
          exact wmax_add hw₁
            (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
            (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
        | om hw₁ hd =>
          exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 (lt_om_selfY hw₁))) hw₁
        | @xi j d hw₁ hK hd =>
          have wd := hw₁.xi.2.1
          have hl : lev π = j := by
            have h1 := lev_le_of_lt_gen hβlt
            have h2 := (lt_M_iffY hw hw₁.xi.1).mp hK
            simp only [lev] at h1 h2
            omega
          have hjn : j ≤ n := by
            have := (lt_M_iffY wπ hn).mp hπK
            omega
          have hb := (lt_xi_psi_iff hl).mp hβlt
          have hdC : inC d d (.Psi π a) = true := ((baseOf_xi_iff j d _).mp hb.2).2
          by_cases hda : Lt d a
          · have hPd := coeffK hn hG ha MIH hw hηK wd (Or.inr hda) _ good d hd (by size_omega)
              (fun w hw' => (fr_spec hw').2) hdC
            exact (MIH d (wkOf hPd (xi_arg_le hw₁ hjn)) hda).1 j hw₁.xi.1 hjn hw₁
          · have had := le_of_not_ltY wd wa hda
            rcases hw.psi_shape with e | ⟨c, e, hs⟩ | ⟨m, δ, e⟩
            · subst e
              exact absurd ((lt_OF_omY (Or.inl ⟨j, d, rfl⟩) hw₁ WNF.zero).mp
                (lt_transY hw₁ hw wπ hβlt hγπ)) (not_lt_zero _)
            · subst e
              have hc := wmax_om_arg hπ
              have hβc := (lt_OF_psiOmY (Or.inl ⟨j, d, rfl⟩) hw₁ hw).mp hβlt
              exact bound _ c (Hull.xi hw₁ hK hd) hc (cxY hw hs)
                (Lt.asymmY hw₁ (wmax_wf hc) hβc)
            · have hδa : Lt δ a := hw.psi.act m δ e
              subst e
              have hmj : m = j := hl
              subst hmj
              have hβπ := lt_transY hw₁ hw wπ hβlt hγπ
              have wδ := wπ.xi.2.1
              have hδd : Lt δ d := lt_of_lt_of_leY wδ wa wd hδa had
              have hne : d ≠ δ := fun e => by subst e; exact Lt.irrefl _ hδd
              rcases (lt_xi_xi0 hne).mp hβπ with ⟨hdδ, -⟩ | ⟨-, hn'⟩
              · exact absurd hdδ (Lt.asymmY wδ wd hδd)
              · exact viaXi rfl (Hull.xi hw₁ hK hd) hw₁ (wit_of_not_inC wπ.xi.2.2.2
                  (fun v hv h => lt_transY (wδ.of_mem_subs hv) wδ wd h hδd) hn')
        | @psi κ d hw₁ hσ hκ hd =>
          have wκ := hw₁.psi.piF
          have wd := hw₁.psi.aF
          have hl : lev κ = lev π := by
            have h1 := lev_le_of_lt_gen hσ
            have h2 := lev_le_of_lt_gen hβlt
            simp only [lev] at h1 h2
            omega
          rcases triY wκ wπ with hκπ | rfl | hπκ
          · exfalso
            have hne : κ ≠ π := fun e => Lt.ne hκπ e
            have hb1 := (lt_psi_psi_ltT (κ := κ) (β := d) hl hne (Lt.asymmY wκ wπ hκπ)).mp hβlt
            rw [not_base_of_lt_tgtY hw wκ hw₁.psi.tgt hl.symm hκπ hσ] at hb1
            cases hb1
          · have hda := lt_psi_psi_same.mp hβlt
            have hPd := coeffK hn hG ha MIH hw hηK wd (Or.inr hda) _ good d hd (by size_omega)
              (R := .Psi κ d) (fun w hw' => lt_transY (wd.of_mem_subs (fr_spec hw').1) hw₁ hw
                (fr_spec hw').2 hβlt) hw₁.psi.Ca
            have hdS : Le d (succM n) :=
              Or.inr (lt_of_lt_of_leY wd wa (WNF.succM hn) hda ha.2.2)
            exact (MIH d (wkOf hPd hdS) hda).2 κ hπ hπK hw₁
          · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
            have hb := (lt_psi_psi_gtT (κ := κ) (β := d) hl hne hπκ).mp hβlt
            rcases hw.psi_shape with e | ⟨c, e, hs⟩ | ⟨m, δ, e⟩
            · subst e
              rw [(baseOf_om_zero _).mpr (by intro h; cases h)] at hb; cases hb
            · subst e
              have hc := wmax_om_arg hπ
              have hcF := wmax_wf hc
              rcases hw₁.psi_shape with e' | ⟨d', e', -⟩ | ⟨m', p', e'⟩
              · subst e'; exact absurd (lt_om_iffG.mp hπκ) (not_lt_zero c)
              · subst e'
                rw [baseOf_om_psiOmY hw hw₁ (ne_gt_of_le (Or.inr (lt_om_iffG.mp hπκ)))] at hb
                cases hb
              · subst e'
                have hX : IsOF (.Psi (.Xi m' p') d) := Or.inr ⟨m', p', d, rfl⟩
                have hnc : ¬ Lt c (.Psi (.Xi m' p') d) := fun h' => by
                  rw [(baseOf_om_OF hcF hs hX hw₁).mpr h'] at hb; cases hb
                exact bound _ c (Hull.psi hw₁ hσ hκ hd) hc (cxY hw hs) hnc
            · subst e
              rw [baseOf_xi] at hb
              have hk : (cmp (kTerm (m - 1)) (Tm.Psi κ d) == .lt) = true := by
                have := kTerm_lt (n := m) wπ.xi.1 hw₁ rfl rfl hl
                unfold Lt at this; rw [this]; rfl
              rw [hk, Bool.true_and] at hb
              exact viaXi rfl (Hull.psi hw₁ hσ hκ hd) hw₁
                (wit_of_not_inC wπ.xi.2.2.2 (fun _ _ h => h) hb)

end MahloOCF

/-! ## 主定理 -/

namespace MahloOCF

open Tm

/-- 体系全体の標準形は全て最大区別集合に入る -/
theorem wmax_of_WNF : ∀ t : Tm, WNF t → Wmax t
  | .zero, _ => wmax_zero
  | .M _, h => wmax_M _ h.M
  | .plus a b, h => wmax_add h (wmax_of_WNF a h.plus.1) (wmax_of_WNF b h.plus.2.1)
  | .Om a, h => wmax_om a (wmax_of_WNF a h.om.1) h
  | .Xi j a, h => by
    have hj := h.xi.1
    have wa := h.xi.2.1
    have hG := goodM hj (fun i hi _ => wmax_M i hi)
    -- 引数の上限 `a ≤ M_j^+` を使う
    have hS : Le a (succM j) := le_of_ne_gtY wa (WNF.succM hj) h.xi.2.2.1
    exact (coll_wk hj hG a ⟨wmax_hull (wmax_of_WNF a wa) (WNF.M' hj),
      inC_mono_g wa wa (WNF.succM hj) hS h.xi.2.2.2, hS⟩).1 j hj (Nat.le_refl _) h
  | .Psi π a, h => by
    have hP := h.psi
    have hn : 1 ≤ lev π + lev a + 1 := by omega
    have wK := WNF.M' hn
    have hG := goodM hn (fun i hi _ => wmax_M i hi)
    have haK : Lt a (.M (lev π + lev a + 1)) := (lt_M_iffY hP.aF hn).mpr (by omega)
    have hπK : Lt π (.M (lev π + lev a + 1)) := (lt_M_iffY hP.piF hn).mpr (by omega)
    have hWa : WK (lev π + lev a + 1) a :=
      ⟨wmax_hull (wmax_of_WNF a hP.aF) wK, inC_of_ltY _ hP.aF wK haK,
        Or.inr (lt_transY hP.aF wK (WNF.succM hn) haK (M_lt_succM hn))⟩
    exact (coll_wk hn hG a hWa).2 π (wmax_of_WNF π hP.piF) hπK h

/-- 体系全体の整列性：標準形（`isNF t = true`）全体の上の `<` は整礎。`Classical.choice` も大基数の仮定も
    使わない（公理は `propext`・`Quot.sound` だけ。下の `#guard_msgs` で検査） -/
theorem wellFounded_isNF :
    WellFounded (fun a b : {t : Tm // isNF t = true} => Lt a.1 b.1) := by
  refine ⟨fun ⟨t, ht⟩ => ?_⟩
  induction wmax_acc (wmax_of_WNF t ht) with
  | intro t _ ih => exact ⟨_, fun ⟨u, hu⟩ hlt => ih u ⟨wmax_of_WNF u hu, hlt⟩ hu⟩

/-- 計算可能な比較 `MahloOCF.lt` で述べた形 -/
theorem wellFounded_lt_isNF :
    WellFounded (fun a b : {t : Tm // isNF t = true} => MahloOCF.lt a.1 b.1 = true) := by
  have h := wellFounded_isNF
  refine Subrelation.wf (r := fun a b : {t : Tm // isNF t = true} => Lt a.1 b.1) ?_ h
  intro a b hab
  simp only [MahloOCF.lt, beq_iff_eq] at hab
  exact hab

end MahloOCF

/-! `#print axioms` の出力を固定する検査。主定理の依存（`cmp`・`inC`・`isNF`・順序の構文的な性質など全て）が
`Classical.choice` を使うようになるとビルドが失敗する。 -/

/-- info: 'MahloOCF.wellFounded_isNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.wellFounded_isNF
