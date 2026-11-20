import Mahlo.FS.BachPsi

/-! `Ω` の持ち上げ（`lbi_om`）：`LBI x y` で、区間 `(x, y]` に `Ω` の不動点（`M`・`Ξ`・`Ψ_Ξ`）がなければ
`LBI (Ω_{x+1}) (Ω_{y+1})`。 -/

namespace MahloOCF.FS

open Tm

/-- 区間 `(x, y]` に `Ω` の不動点がない -/
def NoOF (x y : Tm) : Prop := ∀ z, WNF z → omegaFixed z = true → Lt x z → Le z y → False

theorem lev_succT_le (y : Tm) : lev (succT y) ≤ max 1 (lev y) := by
  cases y with
  | zero => simp [succT, lev, one]
  | plus a b => simp only [succT, lev]; omega
  | _ => simp only [succT, lev]; omega

/-- `Ω` の不動点 `z` が `Ω_{y+1}` 未満なら `z ≤ y` -/
theorem le_of_OF_lt_om {z y : Tm} (hz : WNF z) (hf : omegaFixed z = true) (hy : WNF y)
    (h : Lt z (.Om (succT y))) : Le z y := by
  apply le_of_not_ltY hy hz
  intro hyz
  rcases fixed_shape hz hf with ⟨m, rfl⟩ | hX
  · have hm := hz.M
    have h1 := (lt_M_iffY hy hm).mp hyz
    have h2 := lev_le_of_lt_gen h
    have h3 := lev_succT_le y
    simp only [lev] at h2
    omega
  · have h1 : Lt (succT y) z := succT_lt_OF hX hy hz hyz
    have h2 : Lt (.Om (succT y)) z := (lt_om_OFG hX hz).mpr h1
    exact Lt.asymmY hz (WNF.om_succT hy) h h2

/-- `Ω` の持ち上げ -/
theorem lbi_om {x y : Tm} (hx : WNF x) (hy : WNF y) (hL : LBI x y) (hN : NoOF x y) :
    LBI (.Om (succT x)) (.Om (succT y)) := by
  have hOx := WNF.om_succT hx
  have hOF : ∀ b, WNF b → omegaFixed b = true → Lt (.Om (succT x)) b → Le b (.Om (succT y)) → False := by
    intro b hb hf h1 h2
    have hxb : Lt x b := lt_transY hx hOx hb (lt_succT_om hx) h1
    have hb2 : Lt b (.Om (succT y)) := by
      rcases h2 with e | h
      · subst e; simp [omegaFixed] at hf
      · exact h
    exact hN b hb hf hxb (le_of_OF_lt_om hb hf hy hb2)
  intro b hb hxb hby
  cases b with
  | zero => exact absurd hxb (not_lt_zero _)
  | plus h r => exact le_f0_of_lt_plus hOx (Or.inr rfl) hb hxb
  | M n => exact absurd (hOF _ hb rfl hxb hby) id
  | Xi n e => exact absurd (hOF _ hb rfl hxb hby) id
  | Om w =>
    have hwF := hb.om.1
    have h1 : Lt (succT x) w := lt_om_iffG.mp hxb
    have h2 : Le w (succT y) := by
      rcases hby with e | h
      · cases e; exact Or.inl rfl
      · exact Or.inr (lt_om_iffG.mp h)
    by_cases hr : omReg w
    · rw [f0_om_reg hr]
      exact Or.inr (lt_om_psiOmG.mpr h1)
    · rw [f0_om_lim hb hr]
      have hwy : Le w y := by
        rcases h2 with e | h
        · exfalso; apply hr; right; rw [e]; exact isSucc_succT y
        · exact le_of_lt_succT hwF hy h
      have hxw : Lt x w := lt_transY hx (succT_WNF hx) hwF (lt_succT x) h1
      exact le_om_of_leY (succT_le_succT hx (wnf_f0 hwF) (hL w hwF hxw hwy))
  | Psi ρ C =>
    rcases hb.psi.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨n, d, rfl⟩
    · exact absurd (lt_om_psiOmG.mp hxb) (not_lt_zero _)
    · have h1 : Lt (succT x) c := lt_om_psiOmG.mp hxb
      have hcF := hb.psi.piF.om.1
      have hpF := predT_WNF hcF hc
      have h2 : Le (succT x) (predT c) :=
        le_of_lt_succT (succT_WNF hx) hpF (by rw [succT_predT hcF hc]; exact h1)
      exact le_transY hOx (wnf_omOf hpF) (wnf_f0 hb) (om_le_omOf hOx hpF h2) (psiOm_f0_ge hb hc)
    · exact absurd (hOF _ hb rfl hxb hby) id

end MahloOCF.FS
