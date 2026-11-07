import Mahlo.Good

/-! `cmp`・`inC`・`baseOf` の正しさ。

`Good` な項について

* `cmp a b = ocmp (val a) (val b)`
* `inC a g d = true ↔ val a ∈ C(val g, val d)`
* `baseOf σ t = true ↔ Base (val σ) (val t)`（`σ` は正則な項）

を、定義の停止性の測度 `(大きさの最大, 大きさの和, 段)` の辞書式順序についての整礎帰納法で同時に示す
（`CmpOK`）。各関数の場合分けは `Mahlo/Compare.lean` の比較の補題に対応する。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen MahloOCF

noncomputable section

/-! ### 順序数の比較 -/

open Classical in
/-- 順序数の比較 -/
def ocmp (x y : Ordinal.{u}) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

theorem ocmp_of_lt {x y : Ordinal.{u}} (h : x < y) : ocmp x y = .lt := by
  unfold ocmp; simp [h]

theorem ocmp_of_eq {x y : Ordinal.{u}} (h : x = y) : ocmp x y = .eq := by
  unfold ocmp; subst h; simp [lt_irrefl]

theorem ocmp_of_gt {x y : Ordinal.{u}} (h : y < x) : ocmp x y = .gt := by
  unfold ocmp; simp [lt_asymm h, ne_of_gt h]

theorem ocmp_eq_lt_iff {x y : Ordinal.{u}} : ocmp x y = .lt ↔ x < y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, lt_asymm h]

theorem ocmp_eq_eq_iff {x y : Ordinal.{u}} : ocmp x y = .eq ↔ x = y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, ne_of_lt h]
  · subst h; simp [ocmp_of_eq rfl]
  · simp [ocmp_of_gt h, ne_of_gt h]

theorem ocmp_eq_gt_iff {x y : Ordinal.{u}} : ocmp x y = .gt ↔ y < x := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, lt_asymm h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, h]

theorem ocmp_swap (x y : Ordinal.{u}) : (ocmp x y).swap = ocmp y x := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_gt h]; rfl
  · subst h; rw [ocmp_of_eq rfl]; rfl
  · rw [ocmp_of_gt h, ocmp_of_lt h]; rfl

/-- 大小が同じなら比較も同じ -/
theorem ocmp_congr {x y x' y' : Ordinal.{u}} (h1 : x < y ↔ x' < y') (h2 : y < x ↔ y' < x') :
    ocmp x y = ocmp x' y' := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_lt (h1.mp h)]
  · subst h
    rw [ocmp_of_eq rfl]
    rcases lt_total x' y' with h' | h' | h'
    · exact absurd (h1.mpr h') (lt_irrefl _)
    · rw [ocmp_of_eq h']
    · exact absurd (h2.mpr h') (lt_irrefl _)
  · rw [ocmp_of_gt h, ocmp_of_gt (h2.mp h)]

theorem ocmp_add_left (a x y : Ordinal.{u}) : ocmp (a + x) (a + y) = ocmp x y :=
  ocmp_congr (add_lt_add_iff_right a) (add_lt_add_iff_right a)

theorem bnot_iff {b : Bool} {P : Prop} (h : b = true ↔ P) : (!b) = true ↔ ¬ P := by
  cases b <;> simp_all

/-! ### 辞書式の測度 -/

/-- 測度の辞書式順序 -/
def Lt3 (p q : Nat × Nat × Nat) : Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) p q

theorem lt3_iff {a b c a' b' c' : Nat} :
    Lt3 (a, b, c) (a', b', c') ↔ a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ c < c') := by
  unfold Lt3
  rw [Prod.lex_def]
  simp only [Prod.lex_def]

theorem lt3_trans {p q r : Nat × Nat × Nat} (h1 : Lt3 p q) (h2 : Lt3 q r) : Lt3 p r := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := q
  obtain ⟨a'', b'', c''⟩ := r
  rw [lt3_iff] at h1 h2 ⊢
  omega

theorem lt3_wf : WellFounded Lt3 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

variable [Setting.{u}]

/-- 測度 `μ` 未満の `cmp`・`inC`・`baseOf` の呼び出しが正しい -/
def CmpOK (μ : Nat × Nat × Nat) : Prop :=
  (∀ a b : Tm, Lt3 (max a.size b.size, a.size + b.size, 6) μ → Good.{u} a → Good.{u} b →
    cmp a b = ocmp (val.{u} a) (val b)) ∧
  (∀ a g d : Tm, Lt3 (max a.size (max g.size d.size), a.size + max g.size d.size, 7) μ →
    Good.{u} a → Good.{u} g → Good.{u} d →
    (inC a g d = true ↔ C (val.{u} g) (val d) (val a))) ∧
  (∀ σ t : Tm, Lt3 (max σ.size t.size, σ.size + t.size, 2) μ → Good.{u} σ →
    isRegTerm σ = true → Good.{u} t → (baseOf σ t = true ↔ Base (val.{u} σ) (val t)))

theorem CmpOK.mono {μ ν : Nat × Nat × Nat} (h : CmpOK.{u} μ) (hν : Lt3 ν μ ∨ ν = μ) :
    CmpOK.{u} ν := by
  have hle : ∀ ρ, Lt3 ρ ν → Lt3 ρ μ := fun ρ hρ => by
    cases hν with
    | inl h' => exact lt3_trans hρ h'
    | inr e => rw [← e]; exact hρ
  exact ⟨fun a b hm => h.1 a b (hle _ hm), fun a g d hm => h.2.1 a g d (hle _ hm),
    fun σ t hm => h.2.2 σ t (hle _ hm)⟩

theorem CmpOK.cmp {μ : Nat × Nat × Nat} (h : CmpOK.{u} μ) {a b : Tm}
    (hm : Lt3 (max a.size b.size, a.size + b.size, 6) μ) (ha : Good.{u} a) (hb : Good.{u} b) :
    MahloOCF.cmp a b = ocmp (val.{u} a) (val b) := h.1 a b hm ha hb

theorem CmpOK.inC {μ : Nat × Nat × Nat} (h : CmpOK.{u} μ) {a g d : Tm}
    (hm : Lt3 (max a.size (max g.size d.size), a.size + max g.size d.size, 7) μ)
    (ha : Good.{u} a) (hg : Good.{u} g) (hd : Good.{u} d) :
    MahloOCF.inC a g d = true ↔ C (val.{u} g) (val d) (val a) := h.2.1 a g d hm ha hg hd

theorem CmpOK.baseOf {μ : Nat × Nat × Nat} (h : CmpOK.{u} μ) {σ t : Tm}
    (hm : Lt3 (max σ.size t.size, σ.size + t.size, 2) μ) (hσ : Good.{u} σ)
    (hr : isRegTerm σ = true) (ht : Good.{u} t) :
    MahloOCF.baseOf σ t = true ↔ Base (val.{u} σ) (val t) := h.2.2 σ t hm hσ hr ht

theorem ocmp_Om {x y : Ordinal.{u}} (hx : x < Λ) (hy : y < Λ) : ocmp (Om x) (Om y) = ocmp x y :=
  ocmp_congr (Om_lt_Om_iff hx hy) (Om_lt_Om_iff hy hx)

theorem val_eq_zero_iff {t : Tm} (h : Good.{u} t) : val.{u} t = 0 ↔ t = .zero := by
  apply Iff.intro
  · intro e
    cases Classical.em (t = .zero) with
    | inl h0 => exact h0
    | inr hne => exact absurd e (ne_of_gt (h.inv.pos hne))
  · intro e; subst e; rfl

/-! ### `inC` -/

theorem inC_step {a g d : Tm}
    (hN : CmpOK.{u} (max a.size (max g.size d.size), a.size + max g.size d.size, 7))
    (ha : Good.{u} a) (hg : Good.{u} g) (hd : Good.{u} d) :
    inC a g d = true ↔ C (val.{u} g) (val d) (val a) := by
  have ia := ha.inv
  have ha' := ha
  cases ha with
  | zero => rw [inC]; exact ⟨fun _ => C_zero _ _, fun _ => rfl⟩
  | M n _ => rw [inC]; exact ⟨fun _ => C_K _ _ n, fun _ => rfl⟩
  | plus x y hx hy _ _ _ =>
    rw [inC, Bool.and_eq_true,
      hN.inC (by simp only [Tm.size]; rw [lt3_iff]; omega) hx hg hd,
      hN.inC (by simp only [Tm.size]; rw [lt3_iff]; omega) hy hg hd]
    have hc := ia.cnf
    rw [summands_plus, List.map_cons] at hc
    show _ ↔ C _ _ (val x + val y)
    apply Iff.intro
    · intro h; exact C_add h.1 h.2
    · intro h
      have hall := (C_iff_cnf hc).mp h
      refine And.intro (hall _ List.mem_cons_self) ?_
      exact (C_iff_cnf hy.inv.cnf).mpr (fun p hp => hall p (List.mem_cons_of_mem _ hp))
  | om x hx hf =>
    rw [inC, hN.inC (by simp only [Tm.size]; rw [lt3_iff]; omega) hx hg hd]
    have hΛ := hx.inv.lt_Λ
    have hlt := hx.inv.nonfixed hf
    apply Iff.intro
    · intro h; exact C_Om hΛ h
    · intro h
      cases lt_or_le (Om (val.{u} x)) (val d) with
      | inl h' => exact C_lt (lt_of_le_of_lt (le_Om hΛ) h')
      | inr h' => exact GenRep_Om (C_gen h (ia.principal rfl) h') hΛ hlt
  | xi n b _ hb hcb _ =>
    have e1 := hN.cmp (a := .Xi n b) (b := d) (by simp only [Tm.size]; rw [lt3_iff]; omega) ha' hd
    have e2 := hN.inC (a := b) (g := g) (d := d) (by simp only [Tm.size]; rw [lt3_iff]; omega)
      hb hg hd
    have e3 := hN.cmp (a := b) (b := g) (by simp only [Tm.size]; rw [lt3_iff]; omega) hb hg
    rw [inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2]
    have hx := (ia.xi n b rfl).1
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Xi n h.2 hcb h.1
    · intro h
      cases lt_or_le (val.{u} (.Xi n b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Xi (C_gen h (ia.principal rfl) h') hx hcb
        exact Or.inr ⟨g'.1, g'.2⟩
  | psi pi b hpi hb hreg _ hn =>
    have e1 := hN.cmp (a := .Psi pi b) (b := d) (by simp only [Tm.size]; rw [lt3_iff]; omega)
      ha' hd
    have epi := hN.inC (a := pi) (g := g) (d := d) (by simp only [Tm.size]; rw [lt3_iff]; omega)
      hpi hg hd
    have eb := hN.inC (a := b) (g := g) (d := d) (by simp only [Tm.size]; rw [lt3_iff]; omega)
      hb hg hd
    have e3 := hN.cmp (a := b) (b := g) (by simp only [Tm.size]; rw [lt3_iff]; omega) hb hg
    rw [inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, epi, eb]
    have hp := ia.psi pi b rfl
    have hπ := (hpi.inv.reg hreg).isReg
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Psi h.2 hπ hp hn h.1.1 h.1.2
    · intro h
      cases lt_or_le (val.{u} (.Psi pi b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Psi (C_gen h (ia.principal rfl) h') hp hn
        exact Or.inr ⟨⟨g'.1, g'.2.1⟩, g'.2.2⟩

/-! ### `baseOf` -/

theorem baseOf_step {σ t : Tm} (hN : CmpOK.{u} (max σ.size t.size, σ.size + t.size, 2))
    (hσ : Good.{u} σ) (hr : isRegTerm σ = true) (ht : Good.{u} t) :
    baseOf σ t = true ↔ Base (val.{u} σ) (val t) := by
  have hσ' := hσ
  cases hσ with
  | om c hc _ =>
    rw [baseOf]
    split
    · rename_i hs
      obtain ⟨gp, hv⟩ := good_predT hc hs
      obtain ⟨go, hvo⟩ := good_omOf gp
      have hsz := size_omOf_predT_lt hs
      rw [beq_iff_eq, hN.cmp (by simp only [Tm.size] at hsz ⊢; rw [lt3_iff]; omega) go ht,
        ocmp_eq_lt_iff, hvo]
      have hcΛ := hc.inv.lt_Λ
      show _ ↔ Base (Om (val c)) (val t)
      rw [hv] at hcΛ ⊢
      exact (base_Om_succ_iff hcΛ).symm
    · rename_i hs
      have h0 : c = .zero := by
        simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hr
        cases hr with
        | inl h => exact h
        | inr h => exact absurd h hs
      subst h0
      show ((Tm.zero == Tm.zero) && (t != .zero)) = true ↔ Base (Om 0) (val t)
      rw [base_Om_zero_iff]
      simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
      rw [← val_eq_zero_iff ht]
      exact ⟨fun h => lt_of_le_of_ne (zero_le _) (fun e => h e.symm),
        fun h e => absurd e (ne_of_gt h)⟩
  | xi m d hm hd _ _ =>
    rw [baseOf]
    obtain ⟨gk, hvk⟩ := good_kTerm.{u} (m - 1)
    have hks := kTerm_size (m - 1)
    rw [Bool.and_eq_true, beq_iff_eq,
      hN.cmp (by simp only [Tm.size] at hks ⊢; rw [hks, lt3_iff]; have := Tm.size_pos d; omega)
        gk ht,
      ocmp_eq_lt_iff, hvk,
      hN.inC (by simp only [Tm.size]; rw [lt3_iff]; omega) hd hd ht]
    exact (base_Xi_iff (hσ'.inv.xi m d rfl).1 (hσ'.inv.xi m d rfl).2).symm
  | _ => simp [isRegTerm] at hr

/-! ### `cmpOmX` -/

theorem cmpOmX_step {a X : Tm} (hN : CmpOK.{u} (max (a.size + 1) X.size, a.size + 1 + X.size, 3))
    (ha : Good.{u} a) (hX : Good.{u} X)
    (hXk : (∃ n b, X = .Xi n b) ∨ (∃ pi b, X = .Psi pi b)) :
    cmpOmX a X = ocmp (Om (val.{u} a)) (val X) := by
  have ia := ha.inv
  have iX := hX.inv
  rw [cmpOmX.eq_def]
  by_cases hf : omegaFixed X = true
  · simp only [hf, ↓reduceIte]
    rw [hN.cmp (by rw [lt3_iff]; omega) ha hX]
    have e := ocmp_Om ia.lt_Λ iX.lt_Λ
    rw [iX.fixed hf] at e
    exact e.symm
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rcases hXk with ⟨n, b, rfl⟩ | ⟨pi, b, rfl⟩
    · simp [omegaFixed] at hf
    · have hX' := hX
      cases hX with
      | psi _ _ hpi _ hreg _ _ =>
        cases pi with
        | Om c =>
          have hpi' := hpi
          cases hpi with
          | om _ hc _ =>
            dsimp only
            rw [hN.cmp (by simp only [Tm.size]; rw [lt3_iff]; omega) ha hc]
            have hp := iX.psi (.Om c) b rfl
            simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hreg
            cases hreg with
            | inl h0 =>
              subst h0
              have hc0 : ocmp (val.{u} a) (val Tm.zero) ≠ .lt :=
                fun h => not_lt_zero _ (ocmp_eq_lt_iff.mp h)
              have hgt : val.{u} (Tm.Psi (.Om .zero) b) < Om (val a) :=
                lt_of_lt_of_le hp (Om_le_Om (zero_le _) ia.lt_Λ)
              rw [ocmp_of_gt hgt]
              simp [hc0]
            | inr hs =>
              obtain ⟨ζ, hζ, hsΛ⟩ := hpi'.inv.om c rfl hs
              have hgt : Om ζ < Psi (Om (val.{u} c)) (val b) := by
                rw [hζ]; exact Psi_Om_succ_gt hsΛ _
              split
              · rename_i h
                have hac : val.{u} a < val c := ocmp_eq_lt_iff.mp (beq_iff_eq.mp h)
                rw [hζ] at hac
                apply Eq.symm
                apply ocmp_of_lt
                exact lt_of_le_of_lt (Om_le_Om (le_of_lt_succ hac)
                  (lt_trans _ _ _ (lt_succ_self ζ) hsΛ)) hgt
              · rename_i h
                have hca : val.{u} c ≤ val a :=
                  le_of_not_lt (fun h' => h (beq_iff_eq.mpr (ocmp_of_lt h')))
                exact (ocmp_of_gt (lt_of_lt_of_le hp (Om_le_Om hca ia.lt_Λ))).symm
        | Xi _ _ => simp [omegaFixed, isXi] at hf
        | _ => simp [isRegTerm] at hreg

/-! ### `xiLtXi` -/

theorem xiLtXi_step {n : Nat} {a b : Tm}
    (hN : CmpOK.{u} (max (Tm.Xi n a).size (Tm.Xi n b).size,
      (Tm.Xi n a).size + (Tm.Xi n b).size, 3))
    (ha : Good.{u} (.Xi n a)) (hb : Good.{u} (.Xi n b)) :
    xiLtXi (.Xi n a) (.Xi n b) = true ↔ val.{u} (.Xi n a) < val (.Xi n b) := by
  have hxa := xiGood_of_lt (ha.inv.xi n a rfl).1
  have hxb := xiGood_of_lt (hb.inv.xi n b rfl).1
  have ha' := ha
  have hb' := hb
  cases ha with
  | xi _ _ _ ha hca _ =>
    cases hb with
    | xi _ _ _ hb hcb _ =>
      simp only [Tm.size] at hN
      have e2 := hN.inC (a := a) (g := b) (d := .Xi n b)
        (by simp only [Tm.size]; rw [lt3_iff]; omega) ha hb hb'
      have e4 := hN.inC (a := b) (g := a) (d := .Xi n a)
        (by simp only [Tm.size]; rw [lt3_iff]; omega) hb ha ha'
      rw [xiLtXi, hN.cmp (by rw [lt3_iff]; omega) ha hb, hN.cmp (by rw [lt3_iff]; omega) hb ha]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2, bnot_iff e4]
      exact (Xi_lt_Xi_iff hxa hxb hca hcb).symm

/-! ### `psiLtXi` -/

theorem psiLtXi_step {pi a b : Tm} {m : Nat}
    (hN : CmpOK.{u} (max (Tm.Psi pi a).size (Tm.Xi m b).size,
      (Tm.Psi pi a).size + (Tm.Xi m b).size, 3))
    (hx : Good.{u} (.Psi pi a)) (hy : Good.{u} (.Xi m b)) :
    psiLtXi (.Psi pi a) (.Xi m b) = true ↔ val.{u} (.Psi pi a) < val (.Xi m b) := by
  have hp := hx.inv.psi pi a rfl
  have hXb := hy.inv.xi m b rfl
  have hRT : RegTarget (val.{u} (.Xi m b)) := Or.inr (Or.inr ⟨m, val b, hXb.2, rfl, hXb.1⟩)
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ hpi ha hreg _ _ =>
    simp only [Tm.size] at hN
    have eb := hN.baseOf (σ := .Xi m b) (t := .Psi pi a)
      (by simp only [Tm.size]; rw [lt3_iff]; omega) hy' rfl hx'
    rw [psiLtXi, hN.cmp (by simp only [Tm.size]; rw [lt3_iff]; omega) hpi hy']
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, ocmp_eq_gt_iff, bnot_iff eb]
    rw [not_lt_iff_le]
    show val pi ≤ val (.Xi m b) ∨ ¬ Base (val (.Xi m b)) (Psi (val pi) (val a)) ↔
      Psi (val pi) (val a) < val (.Xi m b)
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact lt_of_lt_of_le hp h
      | inr h =>
        cases lt_or_le (val.{u} (.Xi m b)) (val pi) with
        | inl hlt => exact (Psi_lt_target_iff hp hRT hlt).mpr h
        | inr hle => exact lt_of_lt_of_le hp hle
    · intro h
      cases lt_or_le (val.{u} (.Xi m b)) (val pi) with
      | inl hlt => exact Or.inr ((Psi_lt_target_iff hp hRT hlt).mp h)
      | inr hle => exact Or.inl hle

/-! ### `cmpPsi` -/

theorem cmpPsi_step {pi a sg b : Tm}
    (hN : CmpOK.{u} (max (Tm.Psi pi a).size (Tm.Psi sg b).size,
      (Tm.Psi pi a).size + (Tm.Psi sg b).size, 3))
    (hx : Good.{u} (.Psi pi a)) (hy : Good.{u} (.Psi sg b)) :
    cmpPsi (.Psi pi a) (.Psi sg b) = ocmp (val.{u} (.Psi pi a)) (val (.Psi sg b)) := by
  have px := hx.inv.psi pi a rfl
  have py := hy.inv.psi sg b rfl
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ hpi ha hreg _ hna =>
    cases hy with
    | psi _ _ hsg hb hreg' _ hnb =>
      simp only [Tm.size] at hN
      rw [cmpPsi]
      split
      · rename_i h
        have e := beq_iff_eq.mp h
        subst e
        rw [hN.cmp (by rw [lt3_iff]; omega) ha hb]
        exact ocmp_congr (Psi_lt_Psi_same px py hna hnb).symm (Psi_lt_Psi_same py px hnb hna).symm
      rename_i hne
      have hne' : val.{u} pi ≠ val sg := fun e => hne (beq_iff_eq.mpr (val_inj _ _ hpi hsg e))
      rw [hN.cmp (by rw [lt3_iff]; omega) hsg hpi]
      have ebx := hN.baseOf (σ := sg) (t := .Psi pi a)
        (by simp only [Tm.size]; rw [lt3_iff]; omega) hsg hreg' hx'
      have eby := hN.baseOf (σ := pi) (t := .Psi sg b)
        (by simp only [Tm.size]; rw [lt3_iff]; omega) hpi hreg hy'
      split
      · rename_i h
        have hlt : val.{u} sg < val pi := ocmp_eq_lt_iff.mp (beq_iff_eq.mp h)
        split
        · rename_i hB
          exact (ocmp_of_gt ((Psi_lt_Psi_iff_gt px py hlt).mpr (ebx.mp hB))).symm
        · rename_i hB
          have hB' : ¬ Base (val sg) (val (.Psi pi a)) := fun h' => hB (ebx.mpr h')
          exact (ocmp_of_lt ((Psi_lt_Psi_iff_lt px py hlt).mpr hB')).symm
      · rename_i h
        have hlt : val.{u} pi < val sg := by
          rcases lt_total (val.{u} pi) (val sg) with h' | h' | h'
          · exact h'
          · exact absurd h' hne'
          · exact absurd (beq_iff_eq.mpr (ocmp_of_lt h')) h
        split
        · rename_i hB
          exact (ocmp_of_lt ((Psi_lt_Psi_iff_gt py px hlt).mpr (eby.mp hB))).symm
        · rename_i hB
          have hB' : ¬ Base (val pi) (val (.Psi sg b)) := fun h' => hB (eby.mpr h')
          exact (ocmp_of_gt ((Psi_lt_Psi_iff_lt py px hlt).mpr hB')).symm

/-! ### `cmpP`：和でない項どうしの比較 -/

theorem le3_of {a b c a' b' c' : Nat} (h1 : a ≤ a') (h2 : a = a' → b ≤ b')
    (h3 : a = a' → b = b' → c ≤ c') :
    Lt3 (a, b, c) (a', b', c') ∨ (a, b, c) = (a', b', c') := by
  by_cases e : a = a' ∧ b = b' ∧ c = c'
  · right
    obtain ⟨rfl, rfl, rfl⟩ := e
    rfl
  · left
    rw [lt3_iff]
    omega

theorem cmpP_step {x y : Tm} (hN : CmpOK.{u} (max x.size y.size, x.size + y.size, 4))
    (hx : Good.{u} x) (hy : Good.{u} y) (hxp : isPrincipal x = true)
    (hyp : isPrincipal y = true) :
    cmpP x y = ocmp (val.{u} x) (val y) := by
  have ix := hx.inv
  have iy := hy.inv
  have bx := ix.bounds (ne_zero_of_isPrincipal hxp)
  have bY := iy.bounds (ne_zero_of_isPrincipal hyp)
  have hN3 : CmpOK.{u} (max x.size y.size, x.size + y.size, 3) :=
    hN.mono (Or.inl (by rw [lt3_iff]; omega))
  have hN3' : CmpOK.{u} (max y.size x.size, y.size + x.size, 3) :=
    hN3.mono (le3_of (by omega) (fun _ => by omega) (fun _ _ => by omega))
  rw [cmpP.eq_def]
  by_cases hl : lev x < lev y
  · simp only [hl, ↓reduceIte]
    exact (ocmp_of_lt (lt_of_lt_of_le bx.2.2 (le_trans (K_le (by omega)) bY.2.1))).symm
  by_cases hl' : lev y < lev x
  · simp only [hl, hl', ↓reduceIte]
    exact (ocmp_of_gt (lt_of_lt_of_le bY.2.2 (le_trans (K_le (by omega)) bx.2.1))).symm
  simp only [hl, hl', ↓reduceIte]
  have hlev : lev x = lev y := by omega
  have kx : ∀ n, lev x = n + 1 → (∀ m, x ≠ .M m) → K n < val.{u} x := by
    intro n hn hK
    have h := ix.strict hxp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have ky : ∀ n, lev y = n + 1 → (∀ m, y ≠ .M m) → K n < val.{u} y := by
    intro n hn hK
    have h := iy.strict hyp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have hx' := hx
  have hy' := hy
  cases hx with
  | zero => simp [isPrincipal] at hxp
  | plus => simp [isPrincipal] at hxp
  | M n hn =>
    cases hy with
    | zero => simp [isPrincipal] at hyp
    | plus => simp [isPrincipal] at hyp
    | M m _ =>
      dsimp only
      simp only [lev] at hlev
      have e : n = m := by omega
      subst e
      exact (ocmp_of_eq rfl).symm
    | om b _ hf =>
      dsimp only
      have hK := ky n (by simp only [lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (b == Tm.M n) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        simp [omegaFixed] at hf
      simp only [hne]
      exact (ocmp_of_lt hK).symm
    | xi m c _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | psi pi c _ _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
  | om a ha hf =>
    cases hy with
    | zero => simp [isPrincipal] at hyp
    | plus => simp [isPrincipal] at hyp
    | M m _ =>
      dsimp only
      have hK := kx m (by simp only [lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (a == Tm.M m) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        simp [omegaFixed] at hf
      simp only [hne]
      exact (ocmp_of_gt hK).symm
    | om b hb _ =>
      dsimp only
      rw [hN.cmp (by simp only [Tm.size]; rw [lt3_iff]; omega) ha hb]
      exact (ocmp_Om ha.inv.lt_Λ hb.inv.lt_Λ).symm
    | xi m c _ _ _ _ =>
      dsimp only
      exact cmpOmX_step hN3 ha hy' (Or.inl ⟨m, c, rfl⟩)
    | psi pi c _ _ _ _ _ =>
      dsimp only
      exact cmpOmX_step hN3 ha hy' (Or.inr ⟨pi, c, rfl⟩)
  | xi n a _ ha _ _ =>
    have hXa := ix.xi n a rfl
    cases hy with
    | zero => simp [isPrincipal] at hyp
    | plus => simp [isPrincipal] at hyp
    | M m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ =>
      dsimp only
      rw [cmpOmX_step hN3' hb hx' (Or.inl ⟨n, a, rfl⟩), ocmp_swap]
      rfl
    | xi m b _ hb _ _ =>
      dsimp only
      simp only [lev] at hlev
      subst hlev
      have hXb := iy.xi n b rfl
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (ocmp_of_eq rfl).symm
      · have hab' : ¬ (a == b) = true := by rw [beq_iff_eq]; exact hab
        simp only [hab', Bool.false_eq_true, ↓reduceIte]
        have hiff := xiLtXi_step hN3 hx' hy'
        split
        · rename_i h
          exact (ocmp_of_lt (hiff.mp h)).symm
        · rename_i h
          apply Eq.symm
          apply ocmp_of_gt
          have hne : val.{u} (.Xi n a) ≠ val (.Xi n b) := fun e =>
            hab (val_inj _ _ ha hb (Xi_inj (xiGood_of_lt hXa.1) (xiGood_of_lt hXb.1) hXa.2 hXb.2 e))
          rcases lt_total (val.{u} (.Xi n a)) (val (.Xi n b)) with h' | h' | h'
          · exact absurd (hiff.mpr h') h
          · exact absurd h' hne
          · exact h'
    | psi pi c _ _ _ _ _ =>
      dsimp only
      have hp := iy.psi pi c rfl
      have hiff := psiLtXi_step hN3' hy' hx'
      split
      · rename_i h
        exact (ocmp_of_gt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_lt
        have hne : val.{u} (.Psi pi c) ≠ val (.Xi n a) := Xi_ne_Psi hXa.1 hXa.2 hp
        rcases lt_total (val.{u} (.Psi pi c)) (val (.Xi n a)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
  | psi pi a _ _ _ _ _ =>
    have hp := ix.psi pi a rfl
    cases hy with
    | zero => simp [isPrincipal] at hyp
    | plus => simp [isPrincipal] at hyp
    | M m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ =>
      dsimp only
      rw [cmpOmX_step hN3' hb hx' (Or.inr ⟨pi, a, rfl⟩), ocmp_swap]
      rfl
    | xi m b _ _ _ _ =>
      dsimp only
      have hXb := iy.xi m b rfl
      have hiff := psiLtXi_step hN3 hx' hy'
      split
      · rename_i h
        exact (ocmp_of_lt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_gt
        have hne : val.{u} (.Psi pi a) ≠ val (.Xi m b) := Xi_ne_Psi hXb.1 hXb.2 hp
        rcases lt_total (val.{u} (.Psi pi a)) (val (.Xi m b)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
    | psi sg b _ _ _ _ _ =>
      dsimp only
      exact cmpPsi_step hN3 hx' hy'

/-! ### 和の比較（辞書式） -/

theorem cmpList_step : ∀ (xs ys : List Tm),
    CmpOK.{u} (max (lsize xs) (lsize ys), lsize xs + lsize ys, 5) →
    (∀ t, t ∈ xs → Good.{u} t ∧ isPrincipal t = true) →
    (∀ t, t ∈ ys → Good.{u} t ∧ isPrincipal t = true) →
    CNF (listSum (xs.map val.{u})) (xs.map val) → CNF (listSum (ys.map val.{u})) (ys.map val) →
    cmpList xs ys = ocmp (listSum (xs.map val.{u})) (listSum (ys.map val)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ _ _ hy
    cases ys with
    | nil => rw [cmpList]; exact (ocmp_of_eq rfl).symm
    | cons y ys =>
      rw [cmpList]
      rw [List.map_cons] at hy
      exact (ocmp_of_lt hy.pos).symm
  | cons x xs ih =>
    intro ys hN hxs hys hx hy
    cases ys with
    | nil =>
      rw [cmpList]
      rw [List.map_cons] at hx
      exact (ocmp_of_gt hx.pos).symm
    | cons y ys =>
      simp only [lsize] at hN
      have hx0 := hxs x List.mem_cons_self
      have hy0 := hys y List.mem_cons_self
      have hNP : CmpOK.{u} (max x.size y.size, x.size + y.size, 4) :=
        hN.mono (le3_of (by omega) (fun _ => by omega) (fun _ _ => by omega))
      rw [cmpList, cmpP_step hNP hx0.1 hy0.1 hx0.2 hy0.2]
      simp only [List.map_cons] at hx hy ⊢
      rcases lt_total (val.{u} x) (val y) with h | h | h
      · rw [ocmp_of_lt h]
        exact (ocmp_of_lt (lt_of_lt_of_le (hx.lt_of_head_lt (hy0.1.inv.principal hy0.2) h)
          hy.head_le)).symm
      · rw [ocmp_of_eq h]
        dsimp only
        have hNL : CmpOK.{u} (max (lsize xs) (lsize ys), lsize xs + lsize ys, 5) := by
          have := Tm.size_pos x
          have := Tm.size_pos y
          exact hN.mono (le3_of (by omega) (fun _ => by omega) (fun _ _ => by omega))
        rw [ih ys hNL (fun t ht => hxs t (List.mem_cons_of_mem _ ht))
          (fun t ht => hys t (List.mem_cons_of_mem _ ht)) hx.tail hy.tail,
          listSum_cons, listSum_cons, h, ocmp_add_left]
      · rw [ocmp_of_gt h]
        exact (ocmp_of_gt (lt_of_lt_of_le (hy.lt_of_head_lt (hx0.1.inv.principal hx0.2) h)
          hx.head_le)).symm

theorem cmp_step {a b : Tm} (hN : CmpOK.{u} (max a.size b.size, a.size + b.size, 6))
    (ha : Good.{u} a) (hb : Good.{u} b) : cmp a b = ocmp (val.{u} a) (val b) := by
  have ia := ha.inv
  have ib := hb.inv
  have la := lsize_summands_le a
  have lb := lsize_summands_le b
  have hNL : CmpOK.{u} (max (lsize (summands a)) (lsize (summands b)),
      lsize (summands a) + lsize (summands b), 5) :=
    hN.mono (le3_of (by omega) (fun _ => by omega) (fun _ _ => by omega))
  rw [cmp, cmpList_step _ _ hNL (summands_good a ha) (summands_good b hb)
    ⟨ia.cnf.1, ia.cnf.2.1, rfl⟩ ⟨ib.cnf.1, ib.cnf.2.1, rfl⟩, ← ia.cnf.eq, ← ib.cnf.eq]

/-! ### 帰納法 -/

theorem cmpOK_all (μ : Nat × Nat × Nat) : CmpOK.{u} μ :=
  lt3_wf.induction μ (fun μ ih =>
    ⟨fun _ _ hm ha hb => cmp_step (ih _ hm) ha hb,
     fun _ _ _ hm ha hg hd => inC_step (ih _ hm) ha hg hd,
     fun _ _ hm hσ hr ht => baseOf_step (ih _ hm) hσ hr ht⟩)

/-- `Good` な項について `cmp` は値の比較と一致する -/
theorem cmp_correct {a b : Tm} (ha : Good.{u} a) (hb : Good.{u} b) :
    cmp a b = ocmp (val.{u} a) (val b) :=
  (cmpOK_all (max a.size b.size + 1, 0, 0)).cmp (by rw [lt3_iff]; omega) ha hb

/-- `Good` な項について `inC a g d` は `val a ∈ C(val g, val d)` と一致する -/
theorem inC_correct {a g d : Tm} (ha : Good.{u} a) (hg : Good.{u} g) (hd : Good.{u} d) :
    inC a g d = true ↔ C (val.{u} g) (val d) (val a) :=
  (cmpOK_all (max a.size (max g.size d.size) + 1, 0, 0)).inC (by rw [lt3_iff]; omega) ha hg hd

/-- `Good` な正則項 `σ` について `baseOf σ t` は底の条件と一致する -/
theorem baseOf_correct {σ t : Tm} (hσ : Good.{u} σ) (hr : isRegTerm σ = true) (ht : Good.{u} t) :
    baseOf σ t = true ↔ Base (val.{u} σ) (val t) :=
  (cmpOK_all (max σ.size t.size + 1, 0, 0)).baseOf (by rw [lt3_iff]; omega) hσ hr ht

end

end OCF.Mahlo
