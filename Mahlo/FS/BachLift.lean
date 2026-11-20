import Mahlo.FS.Bach

/-! 区間の下界 `LBI` の持ち上げ（和・`Ω`）と、0 番目の基本的な性質。

* 和：主要項か 0 の `x` より大きい和 `b = h + r` は `x ≤ h ≤ b[0]`（`le_f0_of_lt_plus`）。
  主要項 `h` を前に足しても（吸収なし）`LBI` は保たれる（`lbi_oadd_prin`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 和の 0 番目 -/

/-- 和の 0 番目は先頭以上 -/
theorem head_le_f0 {h r : Tm} (hw : WNF (.plus h r)) : Le h (fund (.plus h r) .zero) := by
  obtain ⟨hh, hr, -, hr0⟩ := hw.plus
  cases hd : dom r with
  | zero => exact absurd ((dom_eq_zero_iff hr).mp hd) hr0
  | one =>
    have hd' : dom (.plus h r) = .one := by rw [dom_plus, hd]
    rw [fund_of_dom_one _ hd']
    exact le_pred hw ((dom_eq_one_iff hw).mp hd') hh (lt_plus_leftY hw)
  | omega =>
    have hd' : dom (.plus h r) = .omega := by rw [dom_plus, hd]
    rw [fund_zero_omega hd', fundNat_plus]
    exact le_oadd_leftW hh (((props_all r hr).1 hd).nf 0)
  | big σ =>
    have hd' : dom (.plus h r) = .big σ := by rw [dom_plus, hd]
    rw [fund_zero_big hd', fundBig_plus]
    have hB := (props_all r hr).2 σ hd
    exact le_oadd_leftW hh (hB.nf _ WNF.zero hB.pos)

/-- 和 `h + r`（`r` が後者でない）の 0 番目 -/
theorem f0_plus {h r : Tm} (hw : WNF (.plus h r)) (hd : dom r ≠ .one) :
    fund (.plus h r) .zero = oadd h (fund r .zero) := by
  obtain ⟨-, hr, -, hr0⟩ := hw.plus
  cases e : dom r with
  | zero => exact absurd ((dom_eq_zero_iff hr).mp e) hr0
  | one => exact absurd e hd
  | omega => rw [fund_zero_omega (by rw [dom_plus, e]), fundNat_plus, fund_zero_omega e]
  | big σ => rw [fund_zero_big (σ := σ) (by rw [dom_plus, e]), fundBig_plus, fund_zero_big e]

/-- 主要項か 0 の `x` より大きい和 `b` は `x ≤ b[0]` -/
theorem le_f0_of_lt_plus {x h r : Tm} (hx : WNF x) (hxp : x = .zero ∨ isPrincipal x = true)
    (hw : WNF (.plus h r)) (hlt : Lt x (.plus h r)) : Le x (fund (.plus h r) .zero) := by
  have hh := hw.plus.1
  have hxh : Le x h := by
    rcases hxp with rfl | hxp
    · exact zero_le h
    · exact (lt_prin_plus_iffY hx hxp hw).mp hlt
  exact le_transY hx hh (wnf_f0 hw) hxh (head_le_f0 hw)

/-- `LBI` の主要項への帰着：`x` が主要項か 0 なら、区間の主要項について示せばよい -/
theorem lbi_of_prin {x y : Tm} (hx : WNF x) (hxp : x = .zero ∨ isPrincipal x = true)
    (h : ∀ b, WNF b → isPrincipal b = true → Lt x b → Le b y → Le x (fund b .zero)) : LBI x y := by
  intro b hb hxb hby
  cases hbp : isPrincipal b
  · cases b with
    | zero => exact absurd hxb (not_lt_zero _)
    | plus h' r => exact le_f0_of_lt_plus hx hxp hb hxb
    | _ => cases hbp
  · exact h b hb hbp hxb hby

theorem LBI.mono {x y y' : Tm} (h : LBI x y) (hy : WNF y) (hy'F : WNF y') (hy' : Le y' y) : LBI x y' :=
  fun b hb hxb hby' => h b hb hxb (le_transY hb hy'F hy hby' hy')

/-! ### 和の持ち上げ -/

/-- 主要項 `h` を前に足しても（吸収なし）区間の下界は保たれる -/
theorem lbi_oadd_prin {h x y : Tm} (hh : WNF h) (hx : WNF x) (hy : WNF y)
    (hxy : Le x y) (hL : LBI x y) (hy0 : y = .zero ∨ WNF (.plus h y)) :
    LBI (oadd h x) (oadd h y) := by
  rcases hy0 with rfl | hhy
  · have hx0 : x = .zero := by
      rcases hxy with e | h'
      · exact e
      · exact absurd h' (not_lt_zero _)
    subst hx0
    rw [oadd_zero]
    exact LBI.refl h hh
  have hxF' := wnf_oadd hh hx
  rw [oadd_plus hhy]
  intro b hb hxb hby
  have hhb : Lt h b := lt_of_le_of_ltY hh hxF' hb (le_oadd_leftW hh hx) hxb
  -- `b = h + y'`（`y' ≤ y`）
  obtain ⟨y', rfl, hy'F, hy'y⟩ : ∃ y', b = .plus h y' ∧ WNF y' ∧ Le y' y := by
    rcases hby with e | hlt
    · exact ⟨y, e, hy, Or.inl rfl⟩
    · rcases lt_plus_cases hhy hb hlt with hle | ⟨y', e, hy'F, hy'y⟩
      · exact absurd hhb (not_lt_of_leY hb hh hle)
      · exact ⟨y', e, hy'F, Or.inr hy'y⟩
  by_cases hx0 : x = .zero
  · subst hx0
    rw [oadd_zero]
    exact head_le_f0 hb
  have hhx : WNF (.plus h x) := by
    rcases hxy with e | hlt
    · subst e; exact hhy
    · exact wnf_plus_of_lt hhy hx hx0 hlt
  rw [oadd_plus hhx] at hxb ⊢
  have hxy' : Lt x y' := lt_plus_plus_same.mp hxb
  have hL' := hL y' hy'F hxy' hy'y
  cases hd : dom y' with
  | one =>
    have hd' : dom (.plus h y') = .one := by rw [dom_plus, hd]
    rw [fund_of_dom_one _ hd']
    exact le_pred hb ((dom_eq_one_iff hb).mp hd') hhx hxb
  | _ =>
    all_goals
      rw [f0_plus hb (by rw [hd]; intro e; cases e), ← oadd_plus hhx]
      exact oadd_le_oadd hh hx (wnf_f0 hy'F) hL'

end MahloOCF.FS
