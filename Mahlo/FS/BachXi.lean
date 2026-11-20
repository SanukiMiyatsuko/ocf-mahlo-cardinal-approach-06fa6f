import Mahlo.FS.BachDiagOut

/-! `Ξ` の持ち上げ：`Ξ_m(A) < b ≤ Ξ_m(A')` の `b` の 0 番目は、`b` が `Ξ_m(E)` か `Ψ_{Ξ_m(E)}(C)` なら
`Ξ_m(E)` の底の 0 番目以上（`b = Ξ_m(E)` なら底そのもの、`Ψ_{Ξ_m(E)}(C)` が底でなければ底以上）、`Ω` の項・
`Ω` への崩壊なら `Ω` の不動点 `Ξ_m(A)` の上。したがって、区間に現れる `E` について
`Ξ_m(A) ≤ base(Ξ_m(E))[0]` なら `LBI (Ξ_m(A)) (Ξ_m(A'))`（`lbi_xi`）。 -/

namespace MahloOCF.FS

open Tm

/-- 底の 0 番目は崩壊 `Ψ_σ(C)` の 0 番目以下 -/
theorem base_f0_le_psi_f0 {σ C : Tm} (hC : WNF (.Psi σ C)) (hb : WNF (base σ)) :
    Le (fund (base σ) .zero) (fund (.Psi σ C) .zero) := by
  by_cases hbb : Tm.Psi σ C = base σ
  · rw [← hbb]; exact Or.inl rfl
  · exact le_transY (wnf_f0 hb) hb (wnf_f0 hC) (f0_le hb) (psi_f0_ge_base hC hbb)

/-- `Ξ` の持ち上げ -/
theorem lbi_xi {m : Nat} {A A' : Tm} (hy : WNF (.Xi m A)) (hy' : WNF (.Xi m A'))
    (hcore : ∀ E, WNF (.Xi m E) → Lt (.Xi m A) (.Xi m E) →
      (Le (.Xi m E) (.Xi m A') ∨ ∃ C, WNF (.Psi (.Xi m E) C) ∧ Lt (.Xi m A) (.Psi (.Xi m E) C) ∧
        Lt (.Psi (.Xi m E) C) (.Xi m A')) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero)) :
    LBI (.Xi m A) (.Xi m A') := by
  have hOF : IsOF (Tm.Xi m A) := Or.inl ⟨m, A, rfl⟩
  have hOF' : IsOF (Tm.Xi m A') := Or.inl ⟨m, A', rfl⟩
  have hlv : ∀ b, Lt (.Xi m A) b → Le b (.Xi m A') → lev b = m := by
    intro b h1 h2
    have e1 : lev (Tm.Xi m A) ≤ lev b := lev_le_of_lt_gen h1
    have e2 : lev b ≤ lev (Tm.Xi m A') := by
      rcases h2 with rfl | h2
      · exact Nat.le_refl _
      · exact lev_le_of_lt_gen h2
    simp only [lev] at e1 e2
    omega
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb hxb hby
  have hl := hlv b hxb hby
  cases b with
  | zero => exact absurd hxb (not_lt_zero _)
  | plus h' r => exact le_f0_of_lt_plus hy (Or.inr rfl) hb hxb
  | M n =>
    exfalso
    have hn := hb.M
    have := (lt_M_iffY hy hn).mp hxb
    simp only [lev] at hl this
    omega
  | Om w =>
    have hwF := hb.om.1
    have hwA : Lt (.Xi m A) w := by
      rcases triY hy hwF with h | e | h
      · exact h
      · exfalso; have := hb.om.2; rw [← e] at this; cases this
      · exact absurd hxb (Lt.asymmY hb hy ((lt_om_OFG hOF hy).mpr h))
    have hwA' : Lt w (.Xi m A') := by
      rcases hby with e | h
      · cases e
      · exact (lt_om_OFG hOF' hy').mp h
    by_cases hr : omReg w
    · rw [f0_om_reg hr]
      rcases hr with h0 | hs
      · rw [h0] at hwA; exact absurd hwA (not_lt_zero _)
      · have hpF := predT_WNF hwF hs
        have hbase : WNF (.Psi (.Om w) .zero) := wnf_base hb (isRegY_of_omReg (Or.inr hs))
        have h1 : Le (.Xi m A) (predT w) :=
          le_of_lt_succT hy hpF (by rw [succT_predT hwF hs]; exact hwA)
        have h2 := le_omOf hpF
        have h3 : Lt (omOf (predT w)) (.Psi (.Om w) .zero) := (baseOf_om_succ hs).mp (base_selfY hbase)
        exact Or.inr (lt_of_le_of_ltY hy (wnf_omOf hpF) hbase
          (le_transY hy hpF (wnf_omOf hpF) h1 h2) h3)
    · rw [f0_om_lim hb hr]
      have hw0 := ih w (by simp only [Tm.size]; omega) hwF hwA (Or.inr hwA')
      have hw0F := wnf_f0 hwF
      exact Or.inr (lt_of_le_of_ltY hy hw0F (WNF.om_succT hw0F) hw0 (lt_succT_om hw0F))
  | Xi n e =>
    have hn : n = m := by simp only [lev] at hl; exact hl
    subst hn
    have hbase := wnf_base hb (Or.inr (Or.inr (Or.inr ⟨n, e, rfl⟩)))
    rw [fund_zero_big (dom_xi n e), fundBig_xi, oadd_zero]
    exact le_transY hy (wnf_f0 hbase) hbase (hcore e hb hxb (Or.inl hby)) (f0_le hbase)
  | Psi ρ C =>
    have hP := hb.psi
    have hρF := hP.piF
    have hby' : Lt (.Psi ρ C) (.Xi m A') := by
      rcases hby with e | h
      · cases e
      · exact h
    rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨n, e, rfl⟩
    · -- `Ω_0` への崩壊は `Ξ_m(A)` 未満
      exfalso
      have h1 : Lt (.Om .zero) (.Xi m A) := (lt_om_OFG hOF hy).mpr (zero_lt (by intro h; cases h))
      have h2 : Lt (.Psi (.Om .zero) C) (.Om .zero) := lt_psiOm_om_self _ _
      exact Lt.irrefl _ (lt_transY hy hb hy hxb (lt_transY hb WNF.om_zero hy h2 h1))
    · -- `Ω_c`（`c` は後者）：0 番目は `Ω_{c-1}` 以上
      have hcF := hρF.om.1
      have hpF := predT_WNF hcF hc
      have h1 : Lt (.Xi m A) (.Om c) := lt_transY hy hb hρF hxb (lt_psiOm_om_self _ _)
      have h2 : Lt (.Xi m A) c := by
        rcases triY hy hcF with h | e | h
        · exact h
        · exfalso; have := hρF.om.2; rw [← e] at this; cases this
        · exact absurd h1 (Lt.asymmY hρF hy ((lt_om_OFG hOF hy).mpr h))
      have h3 : Le (.Xi m A) (predT c) :=
        le_of_lt_succT hy hpF (by rw [succT_predT hcF hc]; exact h2)
      exact le_transY hy (wnf_omOf hpF) (wnf_f0 hb)
        (le_transY hy hpF (wnf_omOf hpF) h3 (le_omOf hpF)) (psiOm_f0_ge hb hc)
    · -- `Ξ_n(e)`：0 番目は `Ξ_n(e)` の底の 0 番目以上
      have hn : n = m := by simp only [lev] at hl; exact hl
      subst hn
      have hxe : Lt (.Xi n A) (.Xi n e) := by
        rcases triY hy hρF with h | h | h
        · exact h
        · exfalso; rw [h] at hxb; exact Lt.asymmY hb hρF (lt_psi_targetY hb) hxb
        · exfalso; exact Lt.asymmY hb hy (lt_transY hb hρF hy (lt_psi_targetY hb) h) hxb
      have hbase := wnf_base hρF (Or.inr (Or.inr (Or.inr ⟨n, e, rfl⟩)))
      exact le_transY hy (wnf_f0 hbase) (wnf_f0 hb)
        (hcore e hρF hxe (Or.inr ⟨C, hb, hxb, hby'⟩)) (base_f0_le_psi_f0 hb hbase)


/-! ### 前線の証人 -/

/-- 前線の証人：`x ∉ C(g, d)` で `x ∈ C(G, D)`（`G` 未満は `g` 未満）なら、`x` の `D` についての前線に
`d` 以上の元がある（`C(g, d)` で失敗する節点への道の上で最初に `D` 未満になる節点） -/
theorem front_witness {d D g G : Tm} (hd : WNF d) (hgG : ∀ a, WNF a → Lt a G → Lt a g) :
    ∀ x : Tm, WNF x → inC x g d = false → inC x G D = true → ∃ u, u ∈ fr D x ∧ Le d u := by
  intro x
  induction x with
  | zero => intro _ h; rw [inC_zero] at h; cases h
  | M n => intro _ h; rw [inC_M] at h; cases h
  | plus a b iha ihb =>
    intro hx h1 h2
    obtain ⟨haF, hbF, -, -⟩ := hx.plus
    rw [inC_plus] at h1 h2
    simp only [Bool.and_eq_true] at h2
    simp only [fr, List.mem_append]
    cases ha : inC a g d with
    | false =>
      obtain ⟨u, hu, hdu⟩ := iha haF ha h2.1
      exact ⟨u, Or.inl hu, hdu⟩
    | true =>
      rw [ha, Bool.true_and] at h1
      obtain ⟨u, hu, hdu⟩ := ihb hbF h1 h2.2
      exact ⟨u, Or.inr hu, hdu⟩
  | Om a ih =>
    intro hx h1 h2
    rw [inC_om] at h1 h2
    simp only [fr]
    exact ih hx.om.1 h1 h2
  | Xi n a ih =>
    intro hx h1 h2
    have haF := hx.xi.2.1
    have hnd : ¬ Lt (.Xi n a) d := fun h => by
      have := (inC_xi_iff (g := g) (d := d)).mpr (Or.inl h); rw [h1] at this; cases this
    simp only [fr]
    split
    · exact ⟨_, List.mem_singleton_self _, le_of_not_ltY hx hd hnd⟩
    · rename_i hlt
      rcases inC_xi_iff.mp h2 with h | ⟨haC, haG⟩
      · exact absurd h hlt
      · have ha1 : inC a g d = false := by
          cases e : inC a g d with
          | false => rfl
          | true =>
            have := (inC_xi_iff (n := n) (a := a) (g := g) (d := d)).mpr (Or.inr ⟨e, hgG a haF haG⟩)
            rw [h1] at this; cases this
        exact ih haF ha1 haC
  | Psi p a ihp iha =>
    intro hx h1 h2
    have hP := hx.psi
    have hnd : ¬ Lt (.Psi p a) d := fun h => by
      have := (inC_psi_iff (g := g) (d := d)).mpr (Or.inl h); rw [h1] at this; cases this
    simp only [fr]
    split
    · exact ⟨_, List.mem_singleton_self _, le_of_not_ltY hx hd hnd⟩
    · rename_i hlt
      rcases inC_psi_iff.mp h2 with h | ⟨hpC, haC, haG⟩
      · exact absurd h hlt
      · cases hp1 : inC p g d with
        | false =>
          obtain ⟨u, hu, hdu⟩ := ihp hP.piF hp1 hpC
          exact ⟨u, List.mem_append_left _ hu, hdu⟩
        | true =>
          have ha1 : inC a g d = false := by
            cases e : inC a g d with
            | false => rfl
            | true =>
              have := (inC_psi_iff (k := p) (δ := a) (g := g) (d := d)).mpr (Or.inr ⟨hp1, e, hgG a hP.aF haG⟩)
              rw [h1] at this; cases this
          obtain ⟨u, hu, hdu⟩ := iha hP.aF ha1 haC
          exact ⟨u, List.mem_append_right _ hu, hdu⟩

/-! ### 底の族の閉包の 0 番目 -/

/-- 底 `base(Ξ_m(E)) = Ψ_{Ξ_m(E)}(E+1)` の列は前線の最大の元を種とする族の閉包 -/
theorem cs_base_xi {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) :
    cs (.Xi m E) (succT E) = mahloVK m E (info E).sums (.Xi m E) (maxL (frB (.Xi m E) (.Xi m E))) := by
  have hEF := hE.xi.2.1
  have hs : isSucc (succT E) = true := isSucc_succT E
  have hv : validR (.Xi m E) (pred (succT E)) = false := by
    cases e : validR (.Xi m E) (pred (succT E)) with
    | false => rfl
    | true =>
      exfalso
      have h1 : Lt E (predT (succT E)) := ltB_iff.mp e
      rw [predT_succT_eq hEF] at h1
      exact Lt.irrefl _ h1
  exact cs_succ_xi_floor (succT_WNF hEF) hs hv

/-- 底の 0 番目は底の族の閉包の 0 番目 -/
theorem base_f0_eq {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) :
    fund (base (.Xi m E)) .zero =
      (mahloVK m E (info E).sums (.Xi m E) (maxL (frB (.Xi m E) (.Xi m E)))).first := by
  have hbF : WNF (base (.Xi m E)) := wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))
  obtain ⟨hd0, hd1⟩ := dom_psi_ne (π := .Xi m E) (X := sc E) hbF (fun h => by cases h.1)
  show fund (.Psi (.Xi m E) (sc E)) .zero = _
  rw [fund_zero_first hd0 hd1]
  show (cs (.Xi m E) (succT E)).first = _
  rw [cs_base_xi hE]

/-- 底の族の閉包の 0 番目は種（前線の最大の元）より大きい -/
theorem seed_lt_base_f0 {m : Nat} {E p : Tm} (hE : WNF (.Xi m E))
    (hp : maxL (frB (.Xi m E) (.Xi m E)) = some p) : Lt p (fund (base (.Xi m E)) .zero) := by
  have hEF := hE.xi.2.1
  have hRinv : ∀ R, R ∈ summands E → Inv R := fun R hR => inv_of R (summands_WNF E hEF R hR).1
  rw [base_f0_eq hE]
  cases hd : (mahloVK m E (info E).sums (.Xi m E) (maxL (frB (.Xi m E) (.Xi m E)))).dom with
  | zero => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).1
  | one => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).2
  | omega =>
    have F := famNat_floor hE hRinv hd
    unfold SeqD.first; rw [hd]; exact F.seed p hp
  | big σ =>
    have F := famBig_floor hE hRinv hd
    unfold SeqD.first; rw [hd]; exact F.seed p hp

/-- 底の 0 番目は前線の元より大きい -/
theorem front_lt_base_f0 {m : Nat} {E u : Tm} (hE : WNF (.Xi m E)) (hu : u ∈ fr (.Xi m E) (.Xi m E)) :
    Lt u (fund (base (.Xi m E)) .zero) := by
  have hu' : u ∈ frB (.Xi m E) (.Xi m E) := by rw [frB_eq_fr]; exact hu
  have hbF : WNF (base (.Xi m E)) := wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))
  cases hp : maxL (frB (.Xi m E) (.Xi m E)) with
  | none => rw [maxL_none hp] at hu'; cases hu'
  | some p =>
    have hall : ∀ x, x ∈ frB (.Xi m E) (.Xi m E) → WNF x := fun x hx => by
      rw [frB_eq_fr] at hx; exact (fr_elem hE hx).1
    have hup := maxL_le hall hp u hu'
    have hpF := hall p (maxL_mem hp)
    exact lt_of_le_of_ltY (hall u hu') hpF (wnf_f0 hbF) hup (seed_lt_base_f0 hE hp)

/-- `Ξ_m(A) < Ξ_m(E)`（`E < A`、`E ∉ C(A, Ξ_m(A))`）なら `Ξ_m(A) < base(Ξ_m(E))[0]` -/
theorem xi_lt_base_f0_of_notC {m : Nat} {A E : Tm} (hA : WNF (.Xi m A)) (hE : WNF (.Xi m E))
    (hEA : Lt E A) (hC : inC E A (.Xi m A) = false) :
    Lt (.Xi m A) (fund (base (.Xi m E)) .zero) := by
  have hEF := hE.xi.2.1
  have hAF := hA.xi.2.1
  obtain ⟨u, hu, hdu⟩ := front_witness hA (fun a ha haE => lt_transY ha hEF hAF haE hEA)
    E hEF hC (xi_selfY hE)
  have hu' : u ∈ fr (.Xi m E) (.Xi m E) := by
    rw [fr]; simp only [Lt.irrefl, ↓reduceIte]; exact hu
  have huF := (fr_elem hE hu').1
  have hbF : WNF (base (.Xi m E)) := wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))
  exact lt_of_le_of_ltY hA huF (wnf_f0 hbF) hdu (front_lt_base_f0 hE hu')


/-! ### 底の 0 番目の下界：`Ξ_m(E[0]) ≤ base(Ξ_m(E))[0]` -/

/-- 後者 `q` の族の閉包は、種 `P` を `s = max(P, Ξ_m(q-1))` に置き換えても同じ -/
theorem mahloVK_succ_seed {m : Nat} {q : Tm} (qs : DL) (ceil : Tm) (P : Option Tm)
    (hs : isSucc q = true) (hq0 : q ≠ .zero) :
    mahloVK m q qs ceil P = mahloVK m q qs ceil (some (maxO P (.Xi m (pred q)))) := by
  have hmax : maxO (some (maxO P (.Xi m (pred q)))) (.Xi m (pred q)) = maxO P (.Xi m (pred q)) := by
    cases P with
    | none => simp [maxO, ltB_self]
    | some p =>
      cases h : ltB p (.Xi m (pred q)) with
      | true => simp [maxO, h, ltB_self]
      | false => simp [maxO, h]
  unfold mahloVK
  rw [ite_eq_right hq0, ite_eq_left hs, ite_eq_right hq0, ite_eq_left hs]
  simp only [hmax]

/-- 前線の最大の元は標準形で `Ξ_m(E)` 未満の主要項 -/
theorem front_max_spec {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) :
    ∀ p, maxL (frB (.Xi m E) (.Xi m E)) = some p → WNF p ∧ Lt p (.Xi m E) ∧ isPrincipal p = true := by
  intro p hp
  have hpm : p ∈ fr (.Xi m E) (.Xi m E) := by rw [← frB_eq_fr]; exact maxL_mem hp
  obtain ⟨h1, h2, h3, -, -⟩ := fr_elem hE hpm
  exact ⟨h1, h2, h3⟩

/-- 後者 `E` の底の 0 番目は `Ξ_m(E-1)` より大きい -/
theorem xi_pred_lt_base_f0 {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) (hs : isSucc E = true) :
    Lt (.Xi m (predT E)) (fund (base (.Xi m E)) .zero) := by
  have hEF := hE.xi.2.1
  have hE0 : E ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hRinv : ∀ R, R ∈ summands E → Inv R := fun R hR => inv_of R (summands_WNF E hEF R hR).1
  have hyF := xi_pred_wnf hE hs
  have hyρ := xi_pred_lt hE hs
  have hPw := front_max_spec hE
  obtain ⟨hsF, hys, -, hcase⟩ :=
    maxO_spec (P := maxL (frB (.Xi m E) (.Xi m E))) hyF (fun p hp => (hPw p hp).1)
  have hsρ : Lt (maxO (maxL (frB (.Xi m E) (.Xi m E))) (.Xi m (predT E))) (.Xi m E) := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; exact hyρ
    · rw [e]; exact (hPw p hp).2.1
  have hsp : isPrincipal (maxO (maxL (frB (.Xi m E) (.Xi m E))) (.Xi m (predT E))) = true := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; rfl
    · rw [e]; exact (hPw p hp).2.2
  have hP' : ∀ p, some (maxO (maxL (frB (.Xi m E) (.Xi m E))) (.Xi m (predT E))) = some p →
      WNF p ∧ Lt p (.Xi m E) ∧ isPrincipal p = true := fun p hp => by
    cases hp; exact ⟨hsF, hsρ, hsp⟩
  have heq := mahloVK_succ_seed (m := m) (info E).sums (.Xi m E) (maxL (frB (.Xi m E) (.Xi m E))) hs hE0
  rw [base_f0_eq hE, heq]
  show Lt _ (mahloVK m E (info E).sums (.Xi m E)
    (some (maxO (maxL (frB (.Xi m E) (.Xi m E))) (.Xi m (predT E))))).first
  cases hd : (mahloVK m E (info E).sums (.Xi m E)
      (some (maxO (maxL (frB (.Xi m E) (.Xi m E))) (.Xi m (predT E))))).dom with
  | zero => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).1
  | one => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).2
  | omega =>
    have F := famNat_vk_succ hE hs hRinv hP' hd
    unfold SeqD.first; rw [hd]
    exact lt_of_le_of_ltY hyF hsF (F.F 0) hys (F.seed _ rfl)
  | big σ =>
    have F := famBig_vk_succ hE hs hRinv hP' hd
    unfold SeqD.first; rw [hd]
    exact lt_of_le_of_ltY hyF hsF (F.F .zero WNF.zero F.pos) hys (F.seed _ rfl)

/-- 極限 `E` の底の 0 番目は素の近似の 0 番目 `s0` 以上 -/
theorem s0_le_base_f0 {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) (hE0 : E ≠ .zero)
    (hs : ¬ isSucc E = true)
    (hS0F : WNF (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
      (lastS (info E).sums) .zero .zero).first) :
    Le (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums) (lastS (info E).sums)
      .zero .zero).first (fund (base (.Xi m E)) .zero) := by
  have hEF := hE.xi.2.1
  have hRinv : ∀ R, R ∈ summands E → Inv R := fun R hR => inv_of R (summands_WNF E hEF R hR).1
  have hbF : WNF (base (.Xi m E)) := wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))
  have key : fund (base (.Xi m E)) .zero = (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums)
      (lastT (info E).sums) (lastS (info E).sums) .zero .zero).first ∨
      ∃ p, maxL (frB (.Xi m E) (.Xi m E)) = some p ∧ Lt (SeqD.app (.Xi m E) (.xi m)
        (preT (info E).sums) (lastT (info E).sums) (lastS (info E).sums) .zero .zero).first p := by
    rw [base_f0_eq hE]
    unfold mahloVK
    rw [ite_eq_right hE0, ite_eq_right hs]
    dsimp only
    cases hP : maxL (frB (.Xi m E) (.Xi m E)) with
    | none => exact Or.inl rfl
    | some p =>
      dsimp only
      by_cases h1 : ltB p (SeqD.app (.Xi m E) (.xi m) (preT (info E).sums) (lastT (info E).sums)
          (lastS (info E).sums) .zero .zero).first = true
      · left; rw [ite_eq_left h1]
      · right
        refine ⟨p, rfl, ?_⟩
        have hpm : p ∈ fr (.Xi m E) (.Xi m E) := by rw [← frB_eq_fr]; exact maxL_mem hP
        have hpF := (fr_elem hE hpm).1
        rcases triY hS0F hpF with h | h | h
        · exact h
        · exact absurd h (fun he => floor_first_ne hE hE0 hs hRinv hpm he)
        · exact absurd (ltB_iff.mpr h) h1
  rcases key with e | ⟨p, hp, hlt⟩
  · rw [e]; exact Or.inl rfl
  · have hpF := (front_max_spec hE p hp).1
    exact Or.inr (lt_transY hS0F hpF (wnf_f0 hbF) hlt (seed_lt_base_f0 hE hp))

/-- `Ξ_m(E[0]) ≤ base(Ξ_m(E))[0]`（`E ≠ 0`、`E ≠ M_m⁺`）。`Ξ_m(E[0])` は標準形 -/
theorem xi_f0_le_base_f0 {m : Nat} {E : Tm} (hE : WNF (.Xi m E)) (hE0 : E ≠ .zero)
    (hES : E ≠ succM m) :
    WNF (.Xi m (fund E .zero)) ∧ Le (.Xi m (fund E .zero)) (fund (base (.Xi m E)) .zero) := by
  have hEF := hE.xi.2.1
  have hRinv : ∀ R, R ∈ summands E → Inv R := fun R hR => inv_of R (summands_WNF E hEF R hR).1
  by_cases hs : isSucc E = true
  · have hd := (dom_eq_one_iff hEF).mpr hs
    rw [fund_of_dom_one _ hd]
    exact ⟨xi_pred_wnf hE hs, Or.inr (xi_pred_lt_base_f0 hE hs)⟩
  · obtain ⟨R, x0, hsq, hfirst, -, -, -, -, -, hW, hx0⟩ := s0_first_xi hE hE0 hs hES hRinv
    have hRq : R ∈ summands E := by rw [hsq]; simp
    have hRW := summands_WNF E hEF R hRq
    have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsq hRW.2]; exact hs
    have hx0F : WNF x0 := by rw [hx0]; exact wnf_f0 hRW.1
    have he : fund E .zero = xa (summands E).dropLast .zero x0 := by
      rw [f0_split _ hEF hsq hRns, ← hx0]
      show _ = oadd (ofSummands (summands E).dropLast) (nsum .zero x0)
      rw [zero_nsum x0 hx0F]
    rw [he]
    refine ⟨hW, ?_⟩
    rw [← hfirst]
    exact s0_le_base_f0 hE hE0 hs (by rw [hfirst]; exact hW)


/-! ### 引数の区間の下界から底の 0 番目の下界 -/

/-- 引数の区間の下界：`LBI A A'` なら、`A < E ≤ A'` の `E` について `Ξ_m(A) ≤ base(Ξ_m(E))[0]`
（`E[0] = A` なら `Ξ_m(E[0]) ≤ base[0]`、`E[0] > A` なら `E[0]` での帰納法の仮定と
`base(Ξ_m(E[0]))[0] < Ξ_m(E[0]) ≤ base(Ξ_m(E))[0]`） -/
theorem xi_le_base_f0_of_lbi {m : Nat} {A A' : Tm} (hA : WNF (.Xi m A)) (hA'F : WNF A')
    (hA'S : Lt A' (succM m)) (hL : LBI A A') :
    ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Le (.Xi m A) (fund (base (.Xi m E)) .zero) := by
  have hm := hA.xi.1
  have hSF := WNF.succM hm
  intro E hE hAE hEA'
  refine WellFounded.induction wellFounded_isNF
    (C := fun a => WNF (.Xi m a.1) → Lt A a.1 → Le a.1 A' →
      Le (.Xi m A) (fund (base (.Xi m a.1)) .zero))
    ⟨E, hE.xi.2.1⟩ ?_ hE hAE hEA'
  intro ⟨E, hEF⟩ ih hE hAE hEA'
  dsimp only at hE hAE hEA' ⊢
  have hE0 : E ≠ .zero := fun e => by rw [e] at hAE; exact not_lt_zero _ hAE
  have hES : E ≠ succM m := fun e => by
    rw [e] at hEA'
    exact not_lt_of_leY hSF hA'F hEA' hA'S
  obtain ⟨hE0F, hC1⟩ := xi_f0_le_base_f0 hE hE0 hES
  rcases hL E hEF hAE hEA' with e | hlt
  · rw [e]; exact hC1
  · have hf0F := wnf_f0 hEF
    have hf0lt := f0_lt hEF hE0
    have ih' := ih ⟨fund E .zero, hf0F⟩ hf0lt hE0F hlt
      (Or.inr (lt_of_lt_of_leY hf0F hEF hA'F hf0lt hEA'))
    have hreg0 : IsRegY (.Xi m (fund E .zero)) := Or.inr (Or.inr (Or.inr ⟨m, _, rfl⟩))
    have hb0F : WNF (base (.Xi m (fund E .zero))) := wnf_base hE0F hreg0
    have h1 : Lt (fund (base (.Xi m (fund E .zero))) .zero) (.Xi m (fund E .zero)) :=
      lt_transY (wnf_f0 hb0F) hb0F hE0F
        (f0_lt hb0F (by show Tm.Psi _ _ ≠ .zero; intro e; cases e)) (base_lt hE0F hreg0)
    have hy0F := wnf_f0 (wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩))))
    exact le_transY hA hE0F hy0F (Or.inr (lt_of_le_of_ltY hA (wnf_f0 hb0F) hE0F ih' h1)) hC1


/-! ### 核心条件の組み立て -/

/-- 区間 `(Ξ_m(A), Ξ_m(A')]` に現れる `E` の条件 -/
def XiRel (m : Nat) (A A' E : Tm) : Prop :=
  Le (.Xi m E) (.Xi m A') ∨ ∃ C, WNF (.Psi (.Xi m E) C) ∧ Lt (.Xi m A) (.Psi (.Xi m E) C) ∧
    Lt (.Psi (.Xi m E) C) (.Xi m A')

/-- 核心条件の組み立て：`E < A` なら前線の証人（(β)）、`A < E ≤ A'` なら与えられた評価、
`A'` より上の `E` は区間に現れない -/
theorem core_assemble {m : Nat} {A A' : Tm} (hA : WNF (.Xi m A)) (hA' : WNF (.Xi m A'))
    (hin : ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero))
    (habove : ∀ E, WNF (.Xi m E) → Lt A E → Lt (.Xi m A) (.Xi m E) → XiRel m A A' E → ¬ Lt A' E) :
    ∀ E, WNF (.Xi m E) → Lt (.Xi m A) (.Xi m E) → XiRel m A A' E →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero) := by
  intro E hE hlt hrel
  have hAF := hA.xi.2.1
  have hEF := hE.xi.2.1
  have hA'F := hA'.xi.2.1
  rcases triY hAF hEF with h | e | h
  · exact hin E hE h (le_of_not_ltY hA'F hEF (habove E hE h hlt hrel)) hlt
  · subst e; exact absurd hlt (Lt.irrefl _)
  · rcases (lt_xi_xi0 (Lt.ne h).symm).mp hlt with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (Lt.asymmY hEF hAF h)
    · exact Or.inr (xi_lt_base_f0_of_notC hA hE h h2)

/-- `Ξ` の持ち上げ（組み立て済み）：`E ∈ (A, A']` の評価と、`A'` より上の `E` が現れないことから `LBI` -/
theorem lbi_xi_of {m : Nat} {A A' : Tm} (hA : WNF (.Xi m A)) (hA' : WNF (.Xi m A'))
    (hin : ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero))
    (habove : ∀ E, WNF (.Xi m E) → Lt A E → Lt (.Xi m A) (.Xi m E) → XiRel m A A' E → ¬ Lt A' E) :
    LBI (.Xi m A) (.Xi m A') :=
  lbi_xi hA hA' (fun E hE hlt hrel => core_assemble hA hA' hin habove E hE hlt hrel)


/-! ### `Ω` の塔 -/

theorem omOf_fixed {G : Tm} (hf : omegaFixed G = true) : omOf G = G := by
  simp [omOf, hf]

/-- `Ω` の不動点は `Ω_0` より大きい -/
theorem om_zero_lt_fixed {G : Tm} (hG : WNF G) (hf : omegaFixed G = true) : Lt (.Om .zero) G := by
  rcases fixed_shape hG hf with ⟨n, rfl⟩ | hX
  · have hn := hG.M
    exact lt_of_lev_lt' (by simp only [lev]; omega)
  · exact (lt_om_OFG hX hG).mpr (zero_lt (by
      rcases hX with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> intro e <;> cases e))

/-- `Ω` の不動点 `G` の上の区間 `(G, Ω_{G+1}]`：主要項は `Ω_{G+1}` と `Ψ_{Ω_{G+1}}(C)` だけで、0 番目は `G` 以上 -/
theorem lbi_fixed_om {G : Tm} (hG : WNF G) (hf : omegaFixed G = true) :
    LBI G (.Om (succT G)) := by
  have hGo : WNF (.Om (succT G)) := WNF.om_succT hG
  have hGs : WNF (succT G) := succT_WNF hG
  have hs : isSucc (succT G) = true := isSucc_succT G
  have homG : omOf (predT (succT G)) = G := by rw [predT_succT_eq hG]; exact omOf_fixed hf
  refine lbi_of_prin hG (Or.inr (OF_principal hG hf)) (fun b hb hbp h1 h2 => ?_)
  rcases h2 with e | h2
  · rw [e, f0_om_reg (Or.inr hs)]
    have hbase : WNF (.Psi (.Om (succT G)) .zero) := wnf_base hGo (isRegY_of_omReg (Or.inr hs))
    have := (baseOf_om_succ hs).mp (base_selfY hbase)
    rw [homG] at this
    exact Or.inr this
  · cases hbf : omegaFixed b with
    | true => exact absurd h1 (not_lt_of_leY hb hG (le_of_OF_lt_om hb hbf hG h2))
    | false =>
      cases b with
      | zero => exact absurd h1 (not_lt_zero _)
      | M n => simp [omegaFixed] at hbf
      | plus a r => cases hbp
      | Xi n e => simp [omegaFixed] at hbf
      | Om w =>
        exfalso
        have hwF := hb.om.1
        have hw : Lt w (succT G) := lt_om_iffG.mp h2
        have hwG : Le w G := le_of_lt_succT hwF hG hw
        have h3 := om_le_omOf hb hG hwG
        rw [omOf_fixed hf] at h3
        exact not_lt_of_leY hb hG h3 h1
      | Psi ρ C =>
        have hP := hb.psi
        rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨n, d, rfl⟩
        · exfalso
          have h3 : Lt G (.Om .zero) := lt_transY hG hb WNF.om_zero h1 (lt_psiOm_om_self _ _)
          exact Lt.asymmY hG WNF.om_zero h3 (om_zero_lt_fixed hG hf)
        · have hcF := hP.piF.om.1
          have hcle : Le c (succT G) := (lt_psiOm_omY hb hGs).mp h2
          rcases hcle with e | hlt
          · subst e
            have := psiOm_f0_ge hb hs
            rw [homG] at this
            exact this
          · exfalso
            have hcG : Le c G := le_of_lt_succT hcF hG hlt
            have h3 := om_le_omOf hP.piF hG hcG
            rw [omOf_fixed hf] at h3
            have h4 : Lt (.Psi (.Om c) C) G :=
              lt_of_lt_of_leY hb hP.piF hG (lt_psiOm_om_self _ _) h3
            exact Lt.asymmY hG hb h1 h4
        · simp [omegaFixed, isXi] at hbf

/-- `Ω` について閉じた点（`0` か `Ω` の不動点）の上の `Ω` の塔の隣り合う元の区間 -/
theorem lbi_tower {G : Tm} (hG : WNF G) (hcl : G = .zero ∨ omegaFixed G = true) :
    ∀ n, LBI (tower G n) (tower G (n + 1)) := by
  intro n
  induction n with
  | zero =>
    show LBI G (.Om (sc G))
    rcases hcl with rfl | hf
    · exact lbi_zero _
    · exact lbi_fixed_om hG hf
  | succ n ih =>
    show LBI (.Om (sc (tower G n))) (.Om (sc (tower G (n + 1))))
    have hx := wnf_tower hG n
    have hy := wnf_tower hG (n + 1)
    refine lbi_om hx hy ih (fun z hz hzf h1 h2 => ?_)
    rcases h2 with e | h2
    · rw [e] at hzf; simp [tower, omegaFixed] at hzf
    · exact not_lt_of_leY hz hx (le_of_OF_lt_om hz hzf hx h2) h1


/-! ### 共通の先頭 -/

/-- 共通の先頭 `pre`（加数は `R` 以上）を足しても区間の下界は保たれる -/
theorem lbi_oadd_pre : ∀ (pre : List Tm) {R x y : Tm}, NFL (pre ++ [R]) → WNF x → WNF y →
    Le x y → Lt y R → LBI x y → LBI (oadd (ofSummands pre) x) (oadd (ofSummands pre) y)
  | [], R, x, y, _, hx, hy, _, _, hL => by
    show LBI (oadd .zero x) (oadd .zero y)
    rw [zero_oadd hx, zero_oadd hy]; exact hL
  | p :: P', R, x, y, hN, hx, hy, hxy, hyR, hL => by
    have hP : NFL (p :: P') := nfl_append_left hN
    have hpW := hP.1 p List.mem_cons_self
    have hR := hN.1 R (by simp)
    have hpR : Le R p := le_of_ne_gtY hR.1 hpW.1 (nfl_append_ge hN p List.mem_cons_self R (by simp))
    have hxR : Lt x R := lt_of_le_of_ltY hx hy hR.1 hxy hyR
    have hk : ∀ z, WNF z → Lt z R → ∀ h r, summands z = h :: r → leB h p = true := by
      intro z hz hzR h r hs
      have hhF := (summands_WNF z hz h (by rw [hs]; exact List.mem_cons_self)).1
      have hhz : Le h z := le_of_mem_summands hz (by rw [hs]; exact List.mem_cons_self)
      exact le_leB (Or.inr (lt_of_lt_of_leY hhF hR.1 hpW.1 (lt_of_le_of_ltY hhF hz hR.1 hhz hzR) hpR))
    have hN' : NFL (P' ++ [R]) := nfl_tail hN
    have ih := lbi_oadd_pre P' hN' hx hy hxy hyR hL
    have hP'F := wnf_ofSummands (nfl_tail hP)
    rw [← oadd_cons_eq hP hx (hk x hx hxR), ← oadd_cons_eq hP hy (hk y hy hyR)]
    have hxF' := wnf_oadd hP'F hx
    have hyF' := wnf_oadd hP'F hy
    refine lbi_oadd_prin hpW.1 hxF' hyF' (oadd_le_oadd hP'F hx hy hxy) ih ?_
    by_cases hy0 : oadd (ofSummands P') y = .zero
    · exact Or.inl hy0
    · refine Or.inr (WNF.mk_plus hpW.1 hyF' hpW.2 hy0 (fun h r hs => ?_))
      have hcp : ∀ s, s ∈ summands (ofSummands P') → leB s p = true := by
        intro s hs'
        rw [summands_ofSummands P' (nfl_principal (nfl_tail hP))] at hs'
        exact leB_iff.mpr (le_head_of_nfl hP s hs')
      exact leB_iff.mp (head_oadd_le hP'F hy hcp (hk y hy hyR) h r hs)


/-! ### 前線による上界 -/

/-- `M_m` 未満の `x` の `M_m` についての前線が全て `y`（階 `m` の `Ω` の不動点、`M_{m-1}` より大きい）未満なら
`x < y` -/
theorem below_of_frM {m : Nat} {y : Tm} (hm : 1 ≤ m) (hyF : WNF y) (hyOF : IsOF y) (hyl : lev y = m)
    (hbot : Lt (floorLev m) y) :
    ∀ x, WNF x → Lt x (.M m) → (∀ w, w ∈ fr (.M m) x → Lt w y) → Lt x y := by
  have hMF := WNF.M' hm
  intro x
  induction x using size_induction with
  | h x ih =>
  intro hx hxM hfr
  have hlev : lev x ≤ m := (lt_M_iffY hx hm).mp hxM
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by rw [hyl]; exact hl)
  cases x with
  | zero => exfalso; simp only [lev] at hl; omega
  | M j => exact lt_of_le_of_ltY hx (wnf_kTerm _) hyF (M_le_floor hx hl) hbot
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hx.plus
    exact (lt_plus_prin_iffY hx hyOF.principal).mpr (ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hx hMF (lt_plus_leftY hx) hxM) (fun w hw => hfr w (fr_mem_plus_l hw)))
  | Om a =>
    have haF := hx.om.1
    exact (lt_om_OFG hyOF hyF).mpr (ih a (by simp only [Tm.size]; omega) haF
      (lt_transY haF hx hMF (lt_om_selfY hx) hxM) (fun w hw => hfr w (fr_mem_om hw)))
  | Xi j a => exact hfr _ (mem_fr_self (Or.inl ⟨j, a, rfl⟩) hxM)
  | Psi q a => exact hfr _ (mem_fr_self (Or.inr ⟨q, a, rfl⟩) hxM)

/-! ### 種なしの近似 `Ξ_m(pre ⊕ x_n)` の梯子 -/

/-! ### 前線の補題 -/

/-- 前線の元の所属：`x ∈ C(g, d)`、`d ≤ R` なら、`x` の `R` についての前線の元は `C(g, d)` に入る -/
theorem inC_fr {g d R : Tm} (hd : WNF d) (hR : WNF R) (hdR : Le d R) :
    ∀ x : Tm, WNF x → inC x g d = true → ∀ f, f ∈ fr R x → inC f g d = true := by
  intro x
  induction x with
  | zero => intro _ _ f hf; simp [fr] at hf
  | M n => intro _ _ f hf; simp [fr] at hf
  | plus a b iha ihb =>
    intro hx h f hf
    obtain ⟨haF, hbF, -, -⟩ := hx.plus
    rw [inC_plus, Bool.and_eq_true] at h
    simp only [fr, List.mem_append] at hf
    rcases hf with hf | hf
    · exact iha haF h.1 f hf
    · exact ihb hbF h.2 f hf
  | Om a ih =>
    intro hx h f hf
    rw [inC_om] at h
    simp only [fr] at hf
    exact ih hx.om.1 h f hf
  | Xi n a ih =>
    intro hx h f hf
    simp only [fr] at hf
    split at hf
    · rw [List.mem_singleton.mp hf]; exact h
    · rename_i hnl
      rcases inC_xi_iff.mp h with h1 | ⟨haC, -⟩
      · exact absurd (lt_of_lt_of_leY hx hd hR h1 hdR) hnl
      · exact ih hx.xi.2.1 haC f hf
  | Psi p a ihp iha =>
    intro hx h f hf
    have hP := hx.psi
    simp only [fr] at hf
    split at hf
    · rw [List.mem_singleton.mp hf]; exact h
    · rename_i hnl
      rcases inC_psi_iff.mp h with h1 | ⟨hpC, haC, -⟩
      · exact absurd (lt_of_lt_of_leY hx hd hR h1 hdR) hnl
      · rcases List.mem_append.mp hf with hf | hf
        · exact ihp hP.piF hpC f hf
        · exact iha hP.aF haC f hf

/-- 補題 K：`Ξ_m(A)` の引数 `A` の `M_m` についての前線の元は `Ξ_m(A)` 未満 -/
theorem fr_lt_xi {m : Nat} {A f : Tm} (hy : WNF (.Xi m A)) (hf : f ∈ fr (.M m) A) :
    Lt f (.Xi m A) := by
  have hm := hy.xi.1
  have hMF := WNF.M' hm
  have hfF := hy.xi.2.1.of_mem_subs (fr_spec hf).1
  have hC := inC_fr hy hMF (Or.inr (xi_lt_M A)) A hy.xi.2.1 (xi_selfY hy) f hf
  exact coll_xi0 hy f hfF hC (fr_spec hf).2

/-- `R` 未満の項の前線の元はその項以下 -/
theorem fr_le_of_lt {R : Tm} (hR : WNF R) : ∀ x : Tm, WNF x → Lt x R → ∀ f, f ∈ fr R x → Le f x := by
  intro x
  induction x with
  | zero => intro _ _ f hf; simp [fr] at hf
  | M n => intro _ _ f hf; simp [fr] at hf
  | plus a b iha ihb =>
    intro hx hxR f hf
    obtain ⟨haF, hbF, -, -⟩ := hx.plus
    have ha : Lt a (.plus a b) := lt_plus_leftY hx
    have hb : Lt b (.plus a b) := lt_plus_rightY hx
    have hfF := hx.of_mem_subs (fr_spec hf).1
    simp only [fr, List.mem_append] at hf
    rcases hf with hf | hf
    · exact Or.inr (lt_of_le_of_ltY hfF haF hx (iha haF (lt_transY haF hx hR ha hxR) f hf) ha)
    · exact Or.inr (lt_of_le_of_ltY hfF hbF hx (ihb hbF (lt_transY hbF hx hR hb hxR) f hf) hb)
  | Om a ih =>
    intro hx hxR f hf
    have haF := hx.om.1
    have ha : Lt a (.Om a) := lt_om_selfY hx
    have hfF := hx.of_mem_subs (fr_spec hf).1
    simp only [fr] at hf
    exact Or.inr (lt_of_le_of_ltY hfF haF hx (ih haF (lt_transY haF hx hR ha hxR) f hf) ha)
  | Xi n a ih =>
    intro hx hxR f hf
    simp only [fr, hxR, ↓reduceIte, List.mem_singleton] at hf
    rw [hf]; exact Or.inl rfl
  | Psi p a ihp iha =>
    intro hx hxR f hf
    simp only [fr, hxR, ↓reduceIte, List.mem_singleton] at hf
    rw [hf]; exact Or.inl rfl

/-- 和の前線は各部分の前線の合併に含まれる -/
theorem fr_oadd_cases {R a y f : Tm} (ha : WNF a) (hy : WNF y) (hf : f ∈ fr R (oadd a y)) :
    f ∈ fr R a ∨ f ∈ fr R y := by
  obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
  cases hs : summands y with
  | nil =>
    rw [eq_zero_of_summands_nil hs, oadd_zero] at hu
    exact Or.inl (mem_fr_iff.mpr ⟨u, hu, hfu⟩)
  | cons h r =>
    rw [summands_oadd hs (nfl_principal (nfl_summands ha)) (nfl_principal (nfl_summands hy))] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact Or.inl (mem_fr_iff.mpr ⟨u, (List.takeWhile_sublist _).subset hu, hfu⟩)
    · exact Or.inr (mem_fr_iff.mpr ⟨u, hu, hfu⟩)

/-! ### 段の補題：新しい引数の前線が下端以下 -/

/-- `Ξ` の持ち上げの 1 段：`A'` の `M_m` についての前線が全て `Ξ_m(A)` 以下なら、`A'` より上の `E` は
区間に現れない。したがって `(A, A']` の `E` の評価だけから `LBI (Ξ_m(A)) (Ξ_m(A'))` -/
theorem lbi_xi_step {m : Nat} {A A' : Tm} (hy : WNF (.Xi m A)) (hy' : WNF (.Xi m A'))
    (hfr : ∀ f, f ∈ fr (.M m) A' → Le f (.Xi m A))
    (hin : ∀ E, WNF (.Xi m E) → Lt A E → Le E A' → Lt (.Xi m A) (.Xi m E) →
      Le (.Xi m A) (fund (base (.Xi m E)) .zero)) :
    LBI (.Xi m A) (.Xi m A') := by
  have hA'F := hy'.xi.2.1
  have hA'M : inC A' A' (.M m) = true := hy'.xi.2.2.2
  refine lbi_xi_of hy hy' hin (fun E hE hAE hlt hrel hA'E => ?_)
  have hEF := hE.xi.2.1
  -- `A' ∈ C(E, Ξ_m(E))`
  have hA'C : inC A' E (.Xi m E) = true :=
    inC_of_fr A' hA'M (fun v hv h => lt_transY (hA'F.of_mem_subs hv) hA'F hEF h hA'E)
      (fun f hf => inC_of_lt_node (fr_node hf)
        (lt_of_le_of_ltY (hA'F.of_mem_subs (fr_spec hf).1) hy hE (hfr f hf) hlt))
  have hnle : ¬ Le (.Xi m E) (.Xi m A') := by
    intro hle
    rcases hle with e | hlt'
    · cases e; exact Lt.irrefl _ hA'E
    · rcases (lt_xi_xi0 (Lt.ne hA'E).symm).mp hlt' with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Lt.asymmY hA'F hEF hA'E h1
      · rw [hA'C] at h2; cases h2
  rcases hrel with hle | ⟨C, hCF, h1, h2⟩
  · exact hnle hle
  · rcases (lt_psi_xiY (π := .Xi m E) (a := C) (b := A') (n := m) rfl).mp h2 with hc | hb
    · exact hnle (le_of_ne_gtY hE hy' hc)
    · have hk : Lt (kTerm (m - 1)) (.Psi (.Xi m E) C) :=
        lt_transY (wnf_kTerm _) hy hCF (floorLev_lt_xi hy) h1
      have hA'C' : inC A' A' (.Psi (.Xi m E) C) = true :=
        inC_of_fr A' hA'M (fun v _ h => h)
          (fun f hf => inC_of_lt_node (fr_node hf)
            (lt_of_le_of_ltY (hA'F.of_mem_subs (fr_spec hf).1) hy hCF (hfr f hf) h1))
      rw [(baseOf_xi_iff m _ _).mpr ⟨hk, hA'C'⟩] at hb
      cases hb


/-- `Ξ` の持ち上げ（下端は階 `m` の `Ω` の不動点 `y`） -/
theorem lbi_xi_gen {m : Nat} {y A' : Tm} (hy : WNF y) (hOF : IsOF y) (hyl : lev y = m)
    (hy' : WNF (.Xi m A'))
    (hcore : ∀ E, WNF (.Xi m E) → Lt y (.Xi m E) →
      (Le (.Xi m E) (.Xi m A') ∨ ∃ C, WNF (.Psi (.Xi m E) C) ∧ Lt y (.Psi (.Xi m E) C) ∧
        Lt (.Psi (.Xi m E) C) (.Xi m A')) →
      Le y (fund (base (.Xi m E)) .zero)) :
    LBI y (.Xi m A') := by
  have hOF' : IsOF (Tm.Xi m A') := Or.inl ⟨m, A', rfl⟩
  have hlv : ∀ b, Lt y b → Le b (.Xi m A') → lev b = m := by
    intro b h1 h2
    have e1 : lev y ≤ lev b := lev_le_of_lt_gen h1
    have e2 : lev b ≤ lev (Tm.Xi m A') := by
      rcases h2 with rfl | h2
      · exact Nat.le_refl _
      · exact lev_le_of_lt_gen h2
    rw [hyl] at e1
    simp only [lev] at e2
    omega
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb hxb hby
  have hl := hlv b hxb hby
  cases b with
  | zero => exact absurd hxb (not_lt_zero _)
  | plus h' r => exact le_f0_of_lt_plus hy (Or.inr hOF.principal) hb hxb
  | M n =>
    exfalso
    have hn := hb.M
    have := (lt_M_iffY hy hn).mp hxb
    rw [hyl] at this
    simp only [lev] at hl
    omega
  | Om w =>
    have hwF := hb.om.1
    have hwA : Lt y w := by
      rcases triY hy hwF with h | e | h
      · exact h
      · exfalso; have := hb.om.2; rw [← e, hOF.fixed] at this; cases this
      · exact absurd hxb (Lt.asymmY hb hy ((lt_om_OFG hOF hy).mpr h))
    have hwA' : Lt w (.Xi m A') := by
      rcases hby with e | h
      · cases e
      · exact (lt_om_OFG hOF' hy').mp h
    by_cases hr : omReg w
    · rw [f0_om_reg hr]
      rcases hr with h0 | hs
      · rw [h0] at hwA; exact absurd hwA (not_lt_zero _)
      · have hpF := predT_WNF hwF hs
        have hbase : WNF (.Psi (.Om w) .zero) := wnf_base hb (isRegY_of_omReg (Or.inr hs))
        have h1 : Le y (predT w) :=
          le_of_lt_succT hy hpF (by rw [succT_predT hwF hs]; exact hwA)
        have h2 := le_omOf hpF
        have h3 : Lt (omOf (predT w)) (.Psi (.Om w) .zero) := (baseOf_om_succ hs).mp (base_selfY hbase)
        exact Or.inr (lt_of_le_of_ltY hy (wnf_omOf hpF) hbase
          (le_transY hy hpF (wnf_omOf hpF) h1 h2) h3)
    · rw [f0_om_lim hb hr]
      have hw0 := ih w (by simp only [Tm.size]; omega) hwF hwA (Or.inr hwA')
      have hw0F := wnf_f0 hwF
      exact Or.inr (lt_of_le_of_ltY hy hw0F (WNF.om_succT hw0F) hw0 (lt_succT_om hw0F))
  | Xi n e =>
    have hn : n = m := by simp only [lev] at hl; exact hl
    subst hn
    have hbase := wnf_base hb (Or.inr (Or.inr (Or.inr ⟨n, e, rfl⟩)))
    rw [fund_zero_big (dom_xi n e), fundBig_xi, oadd_zero]
    exact le_transY hy (wnf_f0 hbase) hbase (hcore e hb hxb (Or.inl hby)) (f0_le hbase)
  | Psi ρ C =>
    have hP := hb.psi
    have hρF := hP.piF
    have hby' : Lt (.Psi ρ C) (.Xi m A') := by
      rcases hby with e | h
      · cases e
      · exact h
    rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨n, e, rfl⟩
    · -- `Ω_0` への崩壊は `Ξ_m(A)` 未満
      exfalso
      have h1 : Lt (.Om .zero) y := (lt_om_OFG hOF hy).mpr (zero_lt hOF.ne_zero)
      have h2 : Lt (.Psi (.Om .zero) C) (.Om .zero) := lt_psiOm_om_self _ _
      exact Lt.irrefl _ (lt_transY hy hb hy hxb (lt_transY hb WNF.om_zero hy h2 h1))
    · -- `Ω_c`（`c` は後者）：0 番目は `Ω_{c-1}` 以上
      have hcF := hρF.om.1
      have hpF := predT_WNF hcF hc
      have h1 : Lt y (.Om c) := lt_transY hy hb hρF hxb (lt_psiOm_om_self _ _)
      have h2 : Lt y c := by
        rcases triY hy hcF with h | e | h
        · exact h
        · exfalso; have := hρF.om.2; rw [← e, hOF.fixed] at this; cases this
        · exact absurd h1 (Lt.asymmY hρF hy ((lt_om_OFG hOF hy).mpr h))
      have h3 : Le y (predT c) :=
        le_of_lt_succT hy hpF (by rw [succT_predT hcF hc]; exact h2)
      exact le_transY hy (wnf_omOf hpF) (wnf_f0 hb)
        (le_transY hy hpF (wnf_omOf hpF) h3 (le_omOf hpF)) (psiOm_f0_ge hb hc)
    · -- `Ξ_n(e)`：0 番目は `Ξ_n(e)` の底の 0 番目以上
      have hn : n = m := by simp only [lev] at hl; exact hl
      subst hn
      have hxe : Lt y (.Xi n e) := by
        rcases triY hy hρF with h | h | h
        · exact h
        · exfalso; rw [h] at hxb; exact Lt.asymmY hb hρF (lt_psi_targetY hb) hxb
        · exfalso; exact Lt.asymmY hb hy (lt_transY hb hρF hy (lt_psi_targetY hb) h) hxb
      have hbase := wnf_base hρF (Or.inr (Or.inr (Or.inr ⟨n, e, rfl⟩)))
      exact le_transY hy (wnf_f0 hbase) (wnf_f0 hb)
        (hcore e hρF hxe (Or.inr ⟨C, hb, hxb, hby'⟩)) (base_f0_le_psi_f0 hb hbase)



/-! ### `Ξ_m` の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])` -/

/-! ### 塔の始点の段 -/

end MahloOCF.FS
