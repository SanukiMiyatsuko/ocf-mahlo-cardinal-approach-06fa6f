import Mahlo.FS.BachOm

/-! Bachmann 性の証明の基本補題：区間の下界 `LBI` の基本形、崩壊の 0 番目の下界（`psi_f0_ge_min`）、
正則項の底（`base σ < b < σ` なら `base σ ≤ b[0]`、`zb_reg`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 基本形 -/

theorem lbi_zero (y : Tm) : LBI .zero y := fun _ _ _ _ => zero_le _

/-- 主要項 `ξ > b` は前の `b` を吸収する -/
theorem oadd_absorb {b ξ : Tm} (hb : WNF b) (hξ : WNF ξ) (hp : isPrincipal ξ = true) (hlt : Lt b ξ) :
    oadd b ξ = ξ := by
  have hs := summands_principal hp
  rw [oadd_eq_ofSummands hb hξ hs]
  cases hb' : summands b with
  | nil => rw [List.takeWhile_nil, List.nil_append]; exact ofSummands_summands ξ hξ
  | cons s rest =>
    have hsmem : s ∈ summands b := by rw [hb']; exact List.mem_cons_self
    have hsF : WNF s := (summands_WNF b hb s hsmem).1
    have hlt' : Lt s ξ := lt_of_le_of_ltY hsF hb hξ (le_of_mem_summands hb hsmem) hlt
    have hf : leB ξ s = false := by
      unfold leB
      rw [swapY hsF hξ, show cmp s ξ = .lt from hlt']
      rfl
    rw [List.takeWhile_cons_of_neg (by simp [hf]), List.nil_append]
    exact ofSummands_summands ξ hξ

theorem psi_le_psi {π a b : Tm} (h : Le a b) : Le (.Psi π a) (.Psi π b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (lt_psi_psi_same.mpr h)

/-- 列が `0`・後者でなければ、0 番目は列の記述の 0 番目 -/
theorem fund_zero_first {t : Tm} (h0 : dom t ≠ .zero) (h1 : dom t ≠ .one) :
    fund t .zero = (info t).seq.first := by
  cases hd : dom t with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [fund_zero_omega hd]
    have hd' : (info t).seq.dom = .omega := hd
    unfold SeqD.first; rw [hd']; rfl
  | big σ =>
    rw [fund_zero_big hd]
    have hd' : (info t).seq.dom = .big σ := hd
    unfold SeqD.first; rw [hd']; rfl

/-! ### 崩壊の 0 番目の下界 -/

/-- `Ξ` の族の閉包（種 `p`）の 0 番目は種より大きい -/
theorem mahloVK_first_gt {m : Nat} {q p : Tm} (hρ : WNF (.Xi m q))
    (hP : WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hSeed : ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
        (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums)
        .zero .zero).first ≠ p → SeedHyp m q p)
    (hB5 : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega) :
    Lt p (mahloVK m q (info q).sums (.Xi m q) (some p)).first := by
  have hqF := hρ.xi.2.1
  have hRinv : ∀ R, R ∈ summands q → Inv R := fun R hR => inv_of R (summands_WNF q hqF R hR).1
  cases hd : (mahloVK m q (info q).sums (.Xi m q) (some p)).dom with
  | zero => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).1
  | one => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).2
  | omega =>
    have F := famNat_mahloVK hρ hRinv (fun p' hp' => by cases hp'; exact hP)
      (fun p' hp' h1 h2 => by cases hp'; exact hSeed h1 h2) (fun p' hp' he => by cases hp'; exact hB5 he) hd
    unfold SeqD.first; rw [hd]; exact F.seed p rfl
  | big σ =>
    have F := famBig_mahloVK hρ hRinv (fun p' hp' => by cases hp'; exact hP)
      (fun p' hp' h1 h2 => by cases hp'; exact hSeed h1 h2) (fun p' hp' he => by cases hp'; exact hB5 he) hd
    unfold SeqD.first; rw [hd]; exact F.seed p rfl

theorem dom_psi_ne {π X : Tm} (ht : WNF (.Psi π X)) (h1 : ¬ (π = .Om .zero ∧ X = .zero)) :
    dom (.Psi π X) ≠ .zero ∧ dom (.Psi π X) ≠ .one := by
  constructor
  · intro e
    exact absurd ((dom_eq_zero_iff ht).mp e) (by intro e'; cases e')
  · intro e
    rw [dom_psi] at e
    exact h1 (dom_one_iff_psi.mp e)

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の 0 番目は `Ψ_{Ξ_m(q)}(X')` より大きい -/
theorem psi_succ_xi_f0_gt {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X)) (hs : isSucc X = true)
    (hqX : Lt q (predT X)) : Lt (.Psi (.Xi m q) (predT X)) (fund (.Psi (.Xi m q) X) .zero) := by
  have hP := ht.psi
  have hρ := hP.piF
  have hXF := hP.aF
  have hpF : WNF (.Psi (.Xi m q) (predT X)) := psi_pred_wnf ht hs (fun n d e => by cases e; exact hqX)
  have hpρ := lt_psi_targetY hpF
  have hv : validR (.Xi m q) (pred X) = true := ltB_iff.mpr hqX
  have hcs := cs_succ_xi hXF hs hv
  have hpred : pred X = predT X := rfl
  rw [hpred] at hcs
  obtain ⟨hd0, hd1⟩ := dom_psi_ne ht (fun h => by cases h.1)
  rw [fund_zero_first hd0 hd1]
  show Lt _ (cs (.Xi m q) X).first
  rw [hcs]
  exact mahloVK_first_gt hρ ⟨hpF, hpρ, rfl⟩ (fun _ _ => seedHyp_valid hpF) (fun he => by
    obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := preT (info q).sums)
      (R := lastT (info q).sums) (r := lastS (info q).sums) (P := .zero) (c := .zero)
    rw [hA] at he; cases he)

/-- 崩壊 `Ψ_σ(C)`（底 `Ψ_σ(C_0)` でない）の 0 番目は底以上 -/
theorem psi_f0_ge_base {σ C : Tm} (hC : WNF (.Psi σ C)) (hne : Tm.Psi σ C ≠ base σ) :
    Le (base σ) (fund (.Psi σ C) .zero) := by
  have hP := hC.psi
  have hCF := hP.aF
  have hσ := hP.piF
  -- 極限の引数：0 番目は標準形の `Ψ_σ(A)`
  have hlim : ¬ isSucc C = true → C ≠ .zero → ∃ A, fund (.Psi σ C) .zero = .Psi σ A ∧ WNF (.Psi σ A) := by
    intro hns hC0
    obtain ⟨pre, R, hsX⟩ := exists_split hC0
    obtain ⟨c, x, he, -, -, -⟩ := psi_lim_f0 hC hsX hns
    have hw := wnf_f0 hC
    rw [he] at hw ⊢
    exact ⟨_, rfl, hw⟩
  rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨m, d, rfl⟩
  · -- `σ = Ω_0`
    have hb : base (.Om .zero) = .Psi (.Om .zero) .zero := rfl
    rw [hb] at hne ⊢
    have hC0 : C ≠ .zero := fun e => hne (by rw [e])
    by_cases hs : isSucc C = true
    · rw [psiOm_succ_f0 hC hs]
      have hpF := psi_pred_WNF hC hs
      exact le_transY (wnf_base WNF.om_zero (Or.inl rfl)) hpF (wnf_mulNat hpF rfl 2)
        (psi_le_psi (zero_le _)) (le_mulNat_two hpF rfl)
    · obtain ⟨A, he, -⟩ := hlim hs hC0
      rw [he]; exact psi_le_psi (zero_le _)
  · -- `σ = Ω_c`（`c` は後者）
    have hb : base (.Om c) = .Psi (.Om c) .zero := rfl
    rw [hb] at hne ⊢
    have hC0 : C ≠ .zero := fun e => hne (by rw [e])
    by_cases hs : isSucc C = true
    · rw [psiOm_succ_f0 hC hs]
      have hpF := psi_pred_WNF hC hs
      exact le_transY (wnf_base hσ (Or.inr (Or.inl ⟨c, rfl, hc⟩))) hpF (wnf_mulNat hpF rfl 2)
        (psi_le_psi (zero_le _)) (le_mulNat_two hpF rfl)
    · obtain ⟨A, he, -⟩ := hlim hs hC0
      rw [he]; exact psi_le_psi (zero_le _)
  · -- `σ = Ξ_m(d)`
    have hb : base (.Xi m d) = .Psi (.Xi m d) (sc d) := rfl
    rw [hb] at hne ⊢
    have hdC : Lt d C := hP.act m d rfl
    have hdF := hσ.xi.2.1
    have hC0 : C ≠ .zero := fun e => by rw [e] at hdC; exact not_lt_zero _ hdC
    by_cases hs : isSucc C = true
    · have hpF' := predT_WNF hCF hs
      have hdp : Le d (predT C) := le_pred_of_lt_succ hCF hs hdF hdC
      have hdp' : Lt d (predT C) := by
        rcases hdp with e | h
        · exfalso; apply hne
          rw [← succT_predT hCF hs, ← e]; rfl
        · exact h
      have hgt := psi_succ_xi_f0_gt hC hs hdp'
      have hpF : WNF (.Psi (.Xi m d) (predT C)) := psi_pred_wnf hC hs (fun n d' e => by cases e; exact hdp')
      exact Or.inr (lt_of_le_of_ltY (wnf_base hσ (Or.inr (Or.inr (Or.inr ⟨m, d, rfl⟩)))) hpF (wnf_f0 hC)
        (psi_le_psi (succT_leY hdF hpF' hdp')) hgt)
    · obtain ⟨A, he, hAw⟩ := hlim hs hC0
      rw [he]
      exact psi_le_psi (succT_leY hdF hAw.psi.aF (hAw.psi.act m d rfl))

/-- `Ξ_m(q)` への崩壊の 0 番目は `M_{m-1}` より大きい -/
theorem floorLev_lt_f0_xi {m : Nat} {q C : Tm} (hC : WNF (.Psi (.Xi m q) C)) :
    Lt (floorLev m) (fund (.Psi (.Xi m q) C) .zero) := by
  have hP := hC.psi
  have hρ := hP.piF
  have hqF := hρ.xi.2.1
  have hbF : WNF (base (.Xi m q)) := wnf_base hρ (Or.inr (Or.inr (Or.inr ⟨m, q, rfl⟩)))
  have hkb : Lt (floorLev m) (base (.Xi m q)) := ((baseOf_xi_iff m q _).mp (base_selfY hbF)).1
  by_cases hfl : Tm.Psi (.Xi m q) C = base (.Xi m q)
  · -- 底：族の閉包の 0 番目
    have hCe : C = sc q := by cases hfl; rfl
    subst hCe
    have hCF := hP.aF
    have hs : isSucc (sc q) = true := isSucc_succT q
    have hv : validR (.Xi m q) (pred (sc q)) = false := by
      cases e : validR (.Xi m q) (pred (sc q)) with
      | false => rfl
      | true =>
        exfalso
        have h1 : Lt q (pred (sc q)) := ltB_iff.mp e
        have h2 : pred (sc q) = q := predT_succT_eq hqF
        rw [h2] at h1; exact Lt.irrefl _ h1
    have hcs := cs_succ_xi_floor hCF hs hv
    have hRinv : ∀ R, R ∈ summands q → Inv R := fun R hR => inv_of R (summands_WNF q hqF R hR).1
    obtain ⟨hd0, hd1⟩ := dom_psi_ne hC (fun h => by cases h.1)
    rw [fund_zero_first hd0 hd1]
    show Lt _ (cs (.Xi m q) (sc q)).first
    rw [hcs]
    cases hd : (mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))).dom with
    | zero => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).1
    | one => exact absurd hd (mahloVK_dom_ne _ _ _ _ _).2
    | omega =>
      have F := famNat_floor hρ hRinv hd
      unfold SeqD.first; rw [hd]; exact F.bot
    | big σ =>
      have F := famBig_floor hρ hRinv hd
      unfold SeqD.first; rw [hd]; exact F.bot
  · exact lt_of_lt_of_leY (wnf_kTerm _) hbF (wnf_f0 hC) hkb (psi_f0_ge_base hC hfl)

/-! ### 正則項の底 -/

/-- `Ω_w` の階が 2 以上なら `w` も同じ階 -/
theorem lev_om_eq {w : Tm} {n : Nat} (h : lev (.Om w) = n) (hn : 2 ≤ n) : lev w = n := by
  have h' : max 1 (lev w) = n := h
  rcases Nat.le_total 1 (lev w) with h1 | h1
  · rw [Nat.max_eq_right h1] at h'; exact h'
  · rw [Nat.max_eq_left h1] at h'; omega

/-- 崩壊先 `σ` の底より大きく `σ` 未満の崩壊 `Ψ_ρ(C)` は、0 番目が底以上 -/
theorem zb_tgt_psi {σ ρ C : Tm} (hσ : WNF σ) (hσT : IsTgt σ) (hb : WNF (.Psi ρ C))
    (h1 : Lt (base σ) (.Psi ρ C)) (h2 : Lt (.Psi ρ C) σ) : Le (base σ) (fund (.Psi ρ C) .zero) := by
  have hbF : WNF (base σ) := wnf_base hσ (IsRegY.tgt hσT)
  have hbe : ∃ a, base σ = .Psi σ a := by
    rcases hσT with rfl | ⟨c, rfl, -⟩ | ⟨n, d, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hbe
  have hρF := hb.psi.piF
  have hl1 : lev (base σ) ≤ lev (.Psi ρ C) := lev_le_of_lt_gen h1
  have hl2 : lev (Tm.Psi ρ C) ≤ lev σ := lev_le_of_lt_gen h2
  have hl : lev σ = lev ρ := by
    rw [ha] at hl1; simp only [lev] at hl1 hl2 ⊢; omega
  rw [ha] at h1 ⊢
  rcases (lt_psi_psiY hl).mp h1 with ⟨e, -⟩ | ⟨hne, hρσ, hnb⟩ | ⟨hne, hnρ, hbt⟩
  · subst e
    rw [← ha]
    exact psi_f0_ge_base hb (fun e => by rw [e, ha] at h1; exact Lt.irrefl _ h1)
  · refine below_range hb (by rw [← ha]; exact hbF) hnb (fun n d e => ?_)
    subst e
    exact kTerm_lt_of_lev (by rw [← ha]; exact hbF) rfl (fun k h => by cases h)
      (by simp only [lev] at hl ⊢; omega)
  · exfalso
    have hσρ : Lt σ ρ := by
      rcases triY hσ hρF with h | h | h
      · exact h
      · exact absurd h hne
      · exact absurd h hnρ
    have := not_base_of_lt_tgtY hb hσ hσT hl.symm hσρ h2
    rw [hbt] at this; cases this

/-- 正則項 `σ` の底 `base σ` と `σ` の間の項 `b` は `base σ ≤ b[0]` -/
theorem zb_reg {σ : Tm} (hσ : WNF σ) (hreg : IsRegY σ) :
    ∀ b, WNF b → Lt (base σ) b → Lt b σ → Le (base σ) (fund b .zero) := by
  have hbF := wnf_base hσ hreg
  have hbp : base σ = .zero ∨ isPrincipal (base σ) = true := by
    rcases hreg with rfl | ⟨c, rfl, -⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
    · exact Or.inr rfl
    · exact Or.inr rfl
    · show kTerm (n - 1) = .zero ∨ isPrincipal (kTerm (n - 1)) = true
      unfold kTerm
      by_cases h : n - 1 = 0
      · rw [ite_eq_left h]; exact Or.inl rfl
      · rw [ite_eq_right h]; exact Or.inr rfl
    · exact Or.inr rfl
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb h1 h2
  cases b with
  | zero => exact absurd h1 (not_lt_zero _)
  | plus h' r => exact le_f0_of_lt_plus hbF hbp hb h1
  | Psi ρ C =>
    rcases hreg with rfl | ⟨c, rfl, hc⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
    · exact zb_tgt_psi hσ (Or.inl rfl) hb h1 h2
    · exact zb_tgt_psi hσ (Or.inr (Or.inl ⟨c, rfl, hc⟩)) hb h1 h2
    · -- `σ = M_n`
      have hn := hσ.M
      by_cases hn1 : n = 1
      · subst hn1; exact zero_le _
      have hbe : base (.M n) = .M (n - 1) := by
        show kTerm (n - 1) = _; unfold kTerm; rw [ite_eq_right (by omega)]
      rw [hbe] at h1 ⊢
      have hlb : lev (Tm.Psi ρ C) = n := by
        have e1 := lev_le_of_lt_gen h1
        have e2 := (lt_M_iffY hb hn).mp h2
        simp only [lev] at e1 e2 ⊢; omega
      have hρF := hb.psi.piF
      rcases hb.psi.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨k, d, rfl⟩
      · exfalso; have h0 : lev (Tm.Psi (.Om .zero) C) = 1 := rfl; rw [h0] at hlb; omega
      · have hcF := hρF.om.1
        have hpF := predT_WNF hcF hc
        have hlc : lev c = n := lev_om_eq (show lev (Tm.Om c) = n from hlb) (by omega)
        have hMF : WNF (.M (n - 1)) := WNF.M' (by omega)
        have hMc : Lt (.M (n - 1)) c := by
          rcases triY hMF hcF with h | e | h
          · exact h
          · exfalso; rw [← e] at hc; cases hc
          · exfalso; have := (lt_M_iffY hcF (by omega)).mp h; omega
        have hMp : Le (.M (n - 1)) (predT c) := le_pred_of_lt_succ hcF hc hMF hMc
        exact le_transY hMF (wnf_omOf hpF) (wnf_f0 hb)
          (le_transY hMF hpF (wnf_omOf hpF) hMp (le_omOf hpF)) (psiOm_f0_ge hb hc)
      · have hk : k = n := by simp only [lev] at hlb; exact hlb
        subst hk
        have := floorLev_lt_f0_xi hb
        have hfl : floorLev k = .M (k - 1) := by unfold floorLev kTerm; rw [ite_eq_right (by omega)]
        rw [hfl] at this
        exact Or.inr this
    · exact zb_tgt_psi hσ (Or.inr (Or.inr ⟨n, p, rfl⟩)) hb h1 h2
  | M j =>
    exfalso
    have hj := hb.M
    rcases hreg with rfl | ⟨c, rfl, hc⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
    · have := lev_le_of_lt_gen h2
      have h0 : lev (Tm.Om .zero) = 1 := rfl; rw [h0] at this; simp only [lev] at this; omega
    · have hcF := hσ.om.1
      have hpF := predT_WNF hcF hc
      have h3 : Le (.M j) (predT c) :=
        le_of_OF_lt_om hb rfl hpF (by rw [succT_predT hcF hc]; exact h2)
      have h4 : Lt (omOf (predT c)) (base (.Om c)) :=
        (baseOf_om_succ hc).mp (base_selfY (wnf_base hσ (Or.inr (Or.inl ⟨c, rfl, hc⟩))))
      exact Lt.irrefl _ (lt_of_le_of_ltY hb (wnf_omOf hpF) hb
        (le_transY hb hpF (wnf_omOf hpF) h3 (le_omOf hpF)) (lt_transY (wnf_omOf hpF) hbF hb h4 h1))
    · have hn := hσ.M
      have e2 := (lt_M_iffY hb hn).mp h2
      simp only [lev] at e2
      by_cases hn1 : n = 1
      · subst hn1; omega
      have hbe : base (.M n) = .M (n - 1) := by
        show kTerm (n - 1) = _; unfold kTerm; rw [ite_eq_right (by omega)]
      rw [hbe] at h1
      have hjn : j = n - 1 := by
        have e1 := (lt_M_iffY (WNF.M' (show 1 ≤ n - 1 by omega)) hj).mp h1
        simp only [lev] at e1; omega
      subst hjn
      exact Lt.irrefl _ h1
    · have e2 := lev_le_of_lt_gen h2
      have e1 := lev_le_of_lt_gen h1
      have hb' : base (.Xi n p) = .Psi (.Xi n p) (sc p) := rfl
      rw [hb'] at e1
      simp only [lev] at e1 e2
      have hk : Lt (kTerm (n - 1)) (base (.Xi n p)) :=
        ((baseOf_xi_iff n p _).mp (base_selfY (show WNF (Tm.Psi (.Xi n p) (sc p)) from hbF))).1
      have hkj : kTerm (n - 1) = .M j := by
        unfold kTerm; rw [ite_eq_right (by omega)]; congr 1; omega
      rw [hkj] at hk
      exact Lt.irrefl _ (lt_transY hb hbF hb hk h1)
  | Om w =>
    have hwF := hb.om.1
    rcases hreg with rfl | ⟨c, rfl, hc⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
    · exfalso; exact not_lt_zero w (lt_om_iffG.mp h2)
    · exfalso
      have hcF := hσ.om.1
      have hpF := predT_WNF hcF hc
      have hwc : Lt w c := lt_om_iffG.mp h2
      have hwp : Le w (predT c) := le_of_lt_succT hwF hpF (by rw [succT_predT hcF hc]; exact hwc)
      have h3 := om_le_omOf hb hpF hwp
      have h4 : Lt (omOf (predT c)) (base (.Om c)) :=
        (baseOf_om_succ hc).mp (base_selfY (wnf_base hσ (Or.inr (Or.inl ⟨c, rfl, hc⟩))))
      exact Lt.irrefl _ (lt_of_le_of_ltY hb (wnf_omOf hpF) hb h3 (lt_transY (wnf_omOf hpF) hbF hb h4 h1))
    · -- `σ = M_n`
      have hn := hσ.M
      by_cases hn1 : n = 1
      · subst hn1; exact zero_le _
      have hbe : base (.M n) = .M (n - 1) := by
        show kTerm (n - 1) = _; unfold kTerm; rw [ite_eq_right (by omega)]
      rw [hbe] at h1 ⊢
      have hMF : WNF (.M (n - 1)) := WNF.M' (by omega)
      have hlb : lev (Tm.Om w) = n := by
        have e1 := lev_le_of_lt_gen h1
        have e2 := (lt_M_iffY hb hn).mp h2
        have e1' : n - 1 + 1 ≤ lev (Tm.Om w) := e1
        omega
      have hlw : lev w = n := lev_om_eq hlb (by omega)
      have hMw : Lt (.M (n - 1)) w := by
        rcases triY hMF hwF with h | e | h
        · exact h
        · exfalso; have := hb.om.2; rw [← e] at this; cases this
        · exfalso; have := (lt_M_iffY hwF (by omega)).mp h; omega
      have hwM : Lt w (.M n) := (lt_M_iffY hwF hn).mpr (by omega)
      by_cases hr : omReg w
      · rw [f0_om_reg hr]
        rcases hr with h0 | hs
        · rw [h0] at hMw; exact absurd hMw (not_lt_zero _)
        · have hpF := predT_WNF hwF hs
          have hbase : WNF (.Psi (.Om w) .zero) := wnf_base hb (isRegY_of_omReg (Or.inr hs))
          have h3 : Lt (omOf (predT w)) (.Psi (.Om w) .zero) := (baseOf_om_succ hs).mp (base_selfY hbase)
          have h4 : Le (.M (n - 1)) (predT w) := le_pred_of_lt_succ hwF hs hMF hMw
          exact Or.inr (lt_of_le_of_ltY hMF (wnf_omOf hpF) hbase
            (le_transY hMF hpF (wnf_omOf hpF) h4 (le_omOf hpF)) h3)
      · rw [f0_om_lim hb hr]
        have hw0 := ih w (by simp only [Tm.size]; omega) hwF (by rw [hbe]; exact hMw) hwM
        rw [hbe] at hw0
        have hw0F := wnf_f0 hwF
        exact Or.inr (lt_of_le_of_ltY hMF hw0F (WNF.om_succT hw0F) hw0 (lt_succT_om hw0F))
    · -- `σ = Ξ_n(p)`：底は `Ω` の不動点
      have hbOF : IsOF (base (.Xi n p)) := Or.inr ⟨n, p, sc p, rfl⟩
      have hbw : Lt (base (.Xi n p)) w := by
        rcases triY hwF hbF with h | e | h
        · exact absurd h1 (Lt.asymmY hb hbF ((lt_om_OFG hbOF hbF).mpr h))
        · exfalso; have := hb.om.2; rw [e, hbOF.fixed] at this; cases this
        · exact h
      have hwσ : Lt w (.Xi n p) := lt_transY hwF hb hσ (lt_om_selfY hb) h2
      by_cases hr : omReg w
      · rw [f0_om_reg hr]
        rcases hr with h0 | hs
        · rw [h0] at hbw; exact absurd hbw (not_lt_zero _)
        · have hpF := predT_WNF hwF hs
          have hbase : WNF (.Psi (.Om w) .zero) := wnf_base hb (isRegY_of_omReg (Or.inr hs))
          have h3 : Lt (omOf (predT w)) (.Psi (.Om w) .zero) := (baseOf_om_succ hs).mp (base_selfY hbase)
          have h4 : Le (base (.Xi n p)) (predT w) := le_pred_of_lt_succ hwF hs hbF hbw
          exact Or.inr (lt_of_le_of_ltY hbF (wnf_omOf hpF) hbase
            (le_transY hbF hpF (wnf_omOf hpF) h4 (le_omOf hpF)) h3)
      · rw [f0_om_lim hb hr]
        have hw0 := ih w (by simp only [Tm.size]; omega) hwF hbw hwσ
        have hw0F := wnf_f0 hwF
        exact Or.inr (lt_of_le_of_ltY hbF hw0F (WNF.om_succT hw0F) hw0 (lt_succT_om hw0F))
  | Xi j e =>
    have hOF : IsOF (Tm.Xi j e) := Or.inl ⟨j, e, rfl⟩
    have hf0 : fund (.Xi j e) .zero = base (.Xi j e) := by
      rw [fund_zero_big (dom_xi j e), fundBig_xi, oadd_zero]
    have hbbF : WNF (base (.Xi j e)) := wnf_base hb (Or.inr (Or.inr (Or.inr ⟨j, e, rfl⟩)))
    rcases hreg with rfl | ⟨c, rfl, hc⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
    · exfalso
      exact Lt.asymmY hb hσ h2 ((lt_om_OFG hOF hb).mpr (zero_lt hOF.ne_zero))
    · exfalso
      have hcF := hσ.om.1
      have hpF := predT_WNF hcF hc
      have h3 : Le (.Xi j e) (predT c) :=
        le_of_OF_lt_om hb rfl hpF (by rw [succT_predT hcF hc]; exact h2)
      have h4 : Lt (omOf (predT c)) (base (.Om c)) :=
        (baseOf_om_succ hc).mp (base_selfY (wnf_base hσ (Or.inr (Or.inl ⟨c, rfl, hc⟩))))
      exact Lt.irrefl _ (lt_of_le_of_ltY hb (wnf_omOf hpF) hb
        (le_transY hb hpF (wnf_omOf hpF) h3 (le_omOf hpF)) (lt_transY (wnf_omOf hpF) hbF hb h4 h1))
    · -- `σ = M_n`
      have hn := hσ.M
      by_cases hn1 : n = 1
      · subst hn1; exact zero_le _
      have hbe : base (.M n) = .M (n - 1) := by
        show kTerm (n - 1) = _; unfold kTerm; rw [ite_eq_right (by omega)]
      rw [hbe] at h1 ⊢
      have hlj : j = n := by
        have e1 := lev_le_of_lt_gen h1
        have e2 := (lt_M_iffY hb hn).mp h2
        simp only [lev] at e1 e2; omega
      subst hlj
      rw [hf0]
      have hk := ((baseOf_xi_iff j e _).mp (base_selfY hbbF)).1
      have hkj : kTerm (j - 1) = .M (j - 1) := by unfold kTerm; rw [ite_eq_right (by omega)]
      rw [hkj] at hk
      exact Or.inr hk
    · -- `σ = Ξ_n(p)`：`Ξ_j(e)` の底は `σ` の底より大きい
      have hb' : base (.Xi n p) = .Psi (.Xi n p) (sc p) := rfl
      have hlj : j = n := by
        have e1 := lev_le_of_lt_gen h1
        have e2 := lev_le_of_lt_gen h2
        rw [hb'] at e1
        simp only [lev] at e1 e2; omega
      subst hlj
      rw [hf0]
      have h1' : Lt (.Psi (.Xi j p) (sc p)) (.Xi j e) := h1
      have hnb : baseOf (.Xi j e) (.Psi (.Xi j p) (sc p)) = false := by
        rcases (lt_psi_xiY (π := .Xi j p) (n := j) rfl).mp h1' with h | h
        · exfalso; apply h
          rw [swapY hb hσ, show cmp (Tm.Xi j e) (.Xi j p) = .lt from h2]; rfl
        · exact h
      have hne : Tm.Xi j p ≠ .Xi j e := fun e' => by rw [e'] at h2; exact Lt.irrefl _ h2
      show Le (Tm.Psi (.Xi j p) (sc p)) (.Psi (.Xi j e) (sc e))
      exact Or.inr ((lt_psi_psiY (π := .Xi j p) (σ := .Xi j e) (a := sc p) (b := sc e)
        (show lev (Tm.Xi j p) = lev (Tm.Xi j e) from rfl)).mpr (Or.inr (Or.inl ⟨hne, h2, hnb⟩)))

end MahloOCF.FS
