import Mahlo.FS.BachReg

/-! Bachmann 性の強い形 `BInv` の枠組み：崩壊以外の項（正則項・和・`Ω_c`（`c` は極限））で示し、全体を崩壊の
場合（`PsiBInv`）に帰着する（`binv_all`）。`BInv` の `ω` 型の部分が梯子 `LadderHyp` を与える。

* `om`：`ω` 型の隣り合う項の区間の下界 `LBI (t[n]) (t[n+1])`。
* `big`：共終数が正則項 `σ` の列は、添字の区間の下界を移す：`ξ ≤ η < σ`、`ξ = 0` か `ξ` は `σ` の底より大きい
  主要項で、`LBI ξ η` なら `LBI (t[ξ]) (t[η])`。 -/

namespace MahloOCF.FS

open Tm

/-- Bachmann 性の強い形 -/
structure BInv (t : Tm) : Prop where
  om : dom t = .omega → ∀ n, LBI (fundNat t n) (fundNat t (n + 1))
  big : ∀ σ, dom t = .big σ → ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ →
    (ξ = .zero ∨ (isPrincipal ξ = true ∧ Lt (base σ) ξ)) → LBI ξ η → LBI (fundBig t ξ) (fundBig t η)

/-! ### 吸収 -/

/-- 先頭の加数 `h` より小さい `b` は吸収される -/
theorem oadd_absorb_gen {b y h : Tm} {r : List Tm} (hb : WNF b) (hy : WNF y) (hs : summands y = h :: r)
    (hlt : Lt b h) : oadd b y = y := by
  have hhF := (summands_WNF y hy h (by rw [hs]; exact List.mem_cons_self)).1
  rw [oadd_eq_ofSummands hb hy hs]
  cases hb' : summands b with
  | nil => rw [List.takeWhile_nil, List.nil_append]; exact ofSummands_summands y hy
  | cons s rest =>
    have hsmem : s ∈ summands b := by rw [hb']; exact List.mem_cons_self
    have hsF : WNF s := (summands_WNF b hb s hsmem).1
    have hlt' : Lt s h := lt_of_le_of_ltY hsF hb hhF (le_of_mem_summands hb hsmem) hlt
    have hf : leB h s = false := by
      unfold leB
      rw [swapY hsF hhF, show cmp s h = .lt from hlt']
      rfl
    rw [List.takeWhile_cons_of_neg (by simp [hf]), List.nil_append]
    exact ofSummands_summands y hy

/-- 主要項 `ξ ≤ η` なら `η` の先頭の加数は `ξ` 以上 -/
theorem prin_le_head {ξ η h : Tm} {r : List Tm} (hξ : WNF ξ) (hη : WNF η) (hp : isPrincipal ξ = true)
    (hs : summands η = h :: r) (hle : Le ξ η) : Le ξ h := by
  have hhF := (summands_WNF η hη h (by rw [hs]; exact List.mem_cons_self)).1
  refine le_of_not_ltY hhF hξ (fun hlt => ?_)
  have hηξ : Lt η ξ := lt_of_summands_lt hη hp (fun u hu => by
    have huF := (summands_WNF η hη u hu).1
    rcases List.mem_cons.mp (hs ▸ hu) with rfl | hu'
    · exact hlt
    · have hn := nfl_summands hη
      rw [hs] at hn
      exact lt_of_le_of_ltY huF hhF hξ (le_of_ne_gtY huF hhF (le_head_of_nfl hn u hu')) hlt)
  exact not_lt_of_leY hξ hη hle hηξ

/-! ### 正則項 -/

/-- 正則項 `σ` の列 `σ[ξ] = base σ ⊕ ξ` は添字の区間の下界を移す -/
theorem lbi_reg_step {σ ξ η : Tm} (hσ : WNF σ) (hreg : IsRegY σ) (hξ : WNF ξ) (hη : WNF η)
    (hξη : Le ξ η) (hησ : Lt η σ) (hadm : ξ = .zero ∨ (isPrincipal ξ = true ∧ Lt (base σ) ξ))
    (hL : LBI ξ η) : LBI (oadd (base σ) ξ) (oadd (base σ) η) := by
  have hbF := wnf_base hσ hreg
  have hσp : isPrincipal σ = true := by
    rcases hreg with rfl | ⟨c, rfl, -⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩ <;> rfl
  rcases hadm with rfl | ⟨hp, hbξ⟩
  · rw [oadd_zero]
    intro b hb h1 h2
    have hbη : Lt (oadd (base σ) η) σ := oadd_lt_prin hbF hη hσp (base_lt hσ hreg) hησ
    exact zb_reg hσ hreg b hb h1 (lt_of_le_of_ltY hb (wnf_oadd hbF hη) hσ h2 hbη)
  · have hη0 : η ≠ .zero := by
      intro e; subst e
      rcases hξη with e | h
      · subst e; cases hp
      · exact not_lt_zero _ h
    obtain ⟨h, r, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hη0)
    have hhF := (summands_WNF η hη h (by rw [hs]; exact List.mem_cons_self)).1
    have hξh := prin_le_head hξ hη hp hs hξη
    rw [oadd_absorb hbF hξ hp hbξ, oadd_absorb_gen hbF hη hs (lt_of_lt_of_leY hbF hξ hhF hbξ hξh)]
    exact hL

theorem binv_reg {σ : Tm} (hσ : WNF σ) (hreg : IsRegY σ) (hd : dom σ = .big σ)
    (hf : ∀ ξ, fundBig σ ξ = oadd (base σ) ξ) : BInv σ := by
  refine ⟨(fun h => by rw [hd] at h; cases h), fun σ' h ξ η hξ hη hξη hησ hadm hL => ?_⟩
  rw [hd] at h
  cases h
  rw [hf, hf]
  exact lbi_reg_step hσ hreg hξ hη hξη hησ hadm hL

/-! ### 和 -/

theorem binv_plus {a b : Tm} (h : WNF (.plus a b)) (hb : BInv b) : BInv (.plus a b) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  have hP := props_all b hbF
  have hy0 : ∀ y, WNF y → Le y b → y = .zero ∨ WNF (.plus a y) := by
    intro y hy hyb
    by_cases e : y = .zero
    · exact Or.inl e
    · rcases hyb with rfl | hlt
      · exact Or.inr h
      · exact Or.inr (wnf_plus_of_lt h hy e hlt)
  refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ hadm hL => ?_⟩
  · rw [dom_plus] at hd
    have hN := hP.1 hd
    rw [fundNat_plus, fundNat_plus]
    exact lbi_oadd_prin ha (hN.nf n) (hN.nf (n + 1)) (Or.inr (hN.mono n)) (hb.om hd n)
      (hy0 _ (hN.nf _) (Or.inr (hN.lt _)))
  · rw [dom_plus] at hd
    have hB := hP.2 σ hd
    have hηF := hB.nf η hη hησ
    have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
    rw [fundBig_plus, fundBig_plus]
    exact lbi_oadd_prin ha (hB.nf ξ hξ hξσ) hηF (bigProps_mono_le hB hξ hη hξη hησ)
      (hb.big σ hd ξ η hξ hη hξη hησ hadm hL) (hy0 _ hηF (Or.inr (hB.lt η hη hησ)))

end MahloOCF.FS

/-! ### `Ω` の不動点のない区間 -/

namespace MahloOCF.FS

open Tm

theorem OF_principal {z : Tm} (hz : WNF z) (hf : omegaFixed z = true) : isPrincipal z = true := by
  rcases fixed_shape hz hf with ⟨m, rfl⟩ | hX
  · rfl
  · exact hX.principal

/-- 主要項 `a` を前に足した区間には `Ω` の不動点がない -/
theorem noOF_plus {a b u v : Tm} (h : WNF (.plus a b)) (hu : WNF u) (hv : WNF v) (hvb : Lt v b) :
    NoOF (oadd a u) (oadd a v) := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  intro z hz hf h1 h2
  have hzp := OF_principal hz hf
  have haz : Lt a z := lt_of_le_of_ltY ha (wnf_oadd ha hu) hz (le_oadd_leftW ha hu) h1
  by_cases hv0 : v = .zero
  · subst hv0
    rw [oadd_zero] at h2
    exact not_lt_of_leY hz ha h2 haz
  · have hav := wnf_plus_of_lt h hv hv0 hvb
    rw [oadd_plus hav] at h2
    rcases h2 with e | h2
    · rw [e] at hzp; cases hzp
    · exact not_lt_of_leY hz ha ((lt_prin_plus_iffY hz hzp hav).mp h2) haz

/-- `Ω` の持ち上げは不動点のない区間を保つ -/
theorem noOF_om {x y : Tm} (hx : WNF x) (hy : WNF y) (hN : NoOF x y) :
    NoOF (.Om (succT x)) (.Om (succT y)) := by
  intro z hz hf h1 h2
  have hxz : Lt x z := lt_transY hx (WNF.om_succT hx) hz (lt_succT_om hx) h1
  have hz2 : Lt z (.Om (succT y)) := by
    rcases h2 with e | h
    · subst e; simp [omegaFixed] at hf
    · exact h
  exact hN z hz hf hxz (le_of_OF_lt_om hz hf hy hz2)

/-- `Ω_k`（`k` は 0 か後者）未満の区間で、下端が `Ω_{k-1}` 以上なら `Ω` の不動点はない -/
theorem noOF_below_om {k x y : Tm} (hk : WNF (.Om k)) (hkr : omReg k) (hy : WNF y)
    (hyk : Lt y (.Om k)) (hx : WNF x)
    (hxlo : ∀ c, isSucc k = true → k = c → Le (omOf (predT c)) x) : NoOF x y := by
  intro z hz hf h1 h2
  have hzk : Lt z (.Om k) := lt_of_le_of_ltY hz hy hk h2 hyk
  rcases hkr with rfl | hs
  · rcases fixed_shape hz hf with ⟨m, rfl⟩ | hX
    · have := lev_le_of_lt_gen hzk
      have hm := hz.M
      have h0 : lev (Tm.Om .zero) = 1 := rfl
      rw [h0] at this
      simp only [lev] at this; omega
    · exact Lt.asymmY hz hk hzk ((lt_om_OFG hX hz).mpr (zero_lt hX.ne_zero))
  · have hkF := hk.om.1
    have hpF := predT_WNF hkF hs
    have h3 : Le z (predT k) := le_of_OF_lt_om hz hf hpF (by rw [succT_predT hkF hs]; exact hzk)
    have h4 := le_transY hz hpF (wnf_omOf hpF) h3 (le_omOf hpF)
    exact not_lt_of_leY hz hx (le_transY hz (wnf_omOf hpF) hx h4 (hxlo k hs rfl)) h1

/-- 不動点でない項の列の隣り合う項・添字の区間には `Ω` の不動点がない -/
theorem noOF_seq : ∀ (c : Tm), WNF c → omegaFixed c = false →
    (dom c = .omega → ∀ n, NoOF (fundNat c n) (fundNat c (n + 1))) ∧
    (∀ σ, dom c = .big σ → ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ →
      NoOF (fundBig c ξ) (fundBig c η)) := by
  intro c
  induction c using size_induction with
  | h c ih =>
  intro hc hnf
  have hP := props_all c hc
  cases c with
  | zero => exact ⟨(fun hd => by cases hd), (fun σ hd => by cases hd)⟩
  | M n => simp [omegaFixed] at hnf
  | Xi n d => simp [omegaFixed] at hnf
  | plus a b =>
    obtain ⟨-, hbF, -, -⟩ := hc.plus
    have hPb := props_all b hbF
    refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ => ?_⟩
    · rw [dom_plus] at hd
      have hN := hPb.1 hd
      rw [fundNat_plus, fundNat_plus]
      exact noOF_plus hc (hN.nf n) (hN.nf (n + 1)) (hN.lt (n + 1))
    · rw [dom_plus] at hd
      have hB := hPb.2 σ hd
      have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
      rw [fundBig_plus, fundBig_plus]
      exact noOF_plus hc (hB.nf ξ hξ hξσ) (hB.nf η hη hησ) (hB.lt η hη hησ)
  | Om e =>
    have heF := hc.om.1
    by_cases hr : omReg e
    · -- 正則項 `Ω_e`：区間は底と `Ω_e` の間
      refine ⟨(fun hd => by rw [dom_om_reg hr] at hd; cases hd), fun σ hd ξ η hξ hη hξη hησ => ?_⟩
      rw [dom_om_reg hr] at hd
      cases hd
      have hreg := isRegY_of_omReg hr
      have hbF := wnf_base hc hreg
      rw [fundBig_om_reg hr, fundBig_om_reg hr]
      have hσp : isPrincipal (Tm.Om e) = true := rfl
      have hyk := oadd_lt_prin hbF hη hσp (base_lt hc hreg) hησ
      refine noOF_below_om hc hr (wnf_oadd hbF hη) hyk (wnf_oadd hbF hξ) (fun c hs he => ?_)
      subst he
      have h1 : Lt (omOf (predT e)) (base (.Om e)) := (baseOf_om_succ hs).mp (base_selfY hbF)
      exact le_transY (wnf_omOf (predT_WNF heF hs)) hbF (wnf_oadd hbF hξ) (Or.inr h1)
        (le_oadd_leftW hbF hξ)
    · have he := ih e (by simp only [Tm.size]; omega) heF hc.om.2
      have hPe := props_all e heF
      refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ => ?_⟩
      · rw [dom_om_lim hr] at hd
        have hN := hPe.1 hd
        rw [fundNat_om hr, fundNat_om hr]
        exact noOF_om (hN.nf n) (hN.nf (n + 1)) (he.1 hd n)
      · rw [dom_om_lim hr] at hd
        have hB := hPe.2 σ hd
        have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
        rw [fundBig_om_lim hr, fundBig_om_lim hr]
        exact noOF_om (hB.nf ξ hξ hξσ) (hB.nf η hη hησ) (he.2 σ hd ξ η hξ hη hξη hησ)
  | Psi π X =>
    have hπF := hc.psi.piF
    rcases hc.psi.tgt with rfl | ⟨k, rfl, hk⟩ | ⟨n, d, rfl⟩
    · -- `Ω_0` への崩壊
      refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ => ?_⟩
      · have hN := hP.1 hd
        exact noOF_below_om hπF (Or.inl rfl) (hN.nf _)
          (lt_transY (hN.nf _) hc hπF (hN.lt _) (lt_psiOm_om_self _ _)) (hN.nf n)
          (fun c hs he => by subst he; cases hs)
      · have hB := hP.2 σ hd
        have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
        exact noOF_below_om hπF (Or.inl rfl) (hB.nf η hη hησ)
          (lt_transY (hB.nf η hη hησ) hc hπF (hB.lt η hη hησ) (lt_psiOm_om_self _ _)) (hB.nf ξ hξ hξσ)
          (fun c hs he => by subst he; cases hs)
    · -- `Ω_k`（`k` は後者）への崩壊：列の項は `Ω_{k-1}` 以上
      have hf0 := psiOm_f0_ge hc hk
      refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ => ?_⟩
      · have hN := hP.1 hd
        rw [fund_zero_omega hd] at hf0
        exact noOF_below_om hπF (Or.inr hk) (hN.nf _)
          (lt_transY (hN.nf _) hc hπF (hN.lt _) (lt_psiOm_om_self _ _)) (hN.nf n)
          (fun c hs he => by
            subst he
            exact le_transY (wnf_omOf (predT_WNF hπF.om.1 hs)) (hN.nf 0) (hN.nf n) hf0
              (natProps_mono_le hN (Nat.zero_le n)))
      · have hB := hP.2 σ hd
        have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
        rw [fund_zero_big hd] at hf0
        exact noOF_below_om hπF (Or.inr hk) (hB.nf η hη hησ)
          (lt_transY (hB.nf η hη hησ) hc hπF (hB.lt η hη hησ) (lt_psiOm_om_self _ _)) (hB.nf ξ hξ hξσ)
          (fun c hs he => by
            subst he
            exact le_transY (wnf_omOf (predT_WNF hπF.om.1 hs)) (hB.nf _ WNF.zero hB.pos)
              (hB.nf ξ hξ hξσ) hf0 (bigProps_mono_le hB WNF.zero hξ (zero_le ξ) hξσ))
    · simp [omegaFixed, isXi] at hnf

/-! ### `Ω_c`（`c` は極限） -/

theorem binv_om_lim {c : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : BInv c) : BInv (.Om c) := by
  have hcF := h.om.1
  have hP := props_all c hcF
  have hN := noOF_seq c hcF h.om.2
  refine ⟨fun hd n => ?_, fun σ hd ξ η hξ hη hξη hησ hadm hL => ?_⟩
  · rw [dom_om_lim hs] at hd
    have hNP := hP.1 hd
    rw [fundNat_om hs, fundNat_om hs]
    exact lbi_om (hNP.nf n) (hNP.nf (n + 1)) (hc.om hd n) (hN.1 hd n)
  · rw [dom_om_lim hs] at hd
    have hB := hP.2 σ hd
    have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hB.σF hξη hησ
    rw [fundBig_om_lim hs, fundBig_om_lim hs]
    exact lbi_om (hB.nf ξ hξ hξσ) (hB.nf η hη hησ) (hc.big σ hd ξ η hξ hη hξη hησ hadm hL)
      (hN.2 σ hd ξ η hξ hη hξη hησ)

/-! ### 全体 -/

/-- 崩壊の場合 -/
def PsiBInv : Prop :=
  ∀ π X, WNF (.Psi π X) → (∀ u, u.size < (Tm.Psi π X).size → WNF u → BInv u) → BInv (.Psi π X)

/-- 崩壊の場合から、全ての標準形の `BInv` -/
theorem binv_all (hψ : PsiBInv) : ∀ t : Tm, WNF t → BInv t := by
  intro t
  induction t using size_induction with
  | h t ih =>
  intro ht
  cases t with
  | zero => exact ⟨(fun hd => by cases hd), (fun σ hd => by cases hd)⟩
  | M n => exact binv_reg ht (IsRegY.M n) (dom_M n) (fundBig_M n)
  | plus a b =>
    obtain ⟨-, hb, -, -⟩ := ht.plus
    exact binv_plus ht (ih b (by simp only [Tm.size]; omega) hb)
  | Om c =>
    by_cases hs : omReg c
    · exact binv_reg ht (isRegY_of_omReg hs) (dom_om_reg hs) (fundBig_om_reg hs)
    · exact binv_om_lim ht hs (ih c (by simp only [Tm.size]; omega) ht.om.1)
  | Xi n d => exact binv_reg ht (Or.inr (Or.inr (Or.inr ⟨n, d, rfl⟩))) (dom_xi n d) (fundBig_xi n d)
  | Psi π X => exact hψ π X ht (fun u hu huF => ih u hu huF)

/-- 崩壊の場合から梯子 -/
theorem ladderHyp_of_binv (hψ : PsiBInv) : LadderHyp :=
  fun t n ht hd => (binv_all hψ t ht).om hd n

/-- 崩壊の場合から Bachmann 性 -/
theorem bachHyp_of_binv (hψ : PsiBInv) : BachHyp := bachHyp_of_ladder (ladderHyp_of_binv hψ)

end MahloOCF.FS
