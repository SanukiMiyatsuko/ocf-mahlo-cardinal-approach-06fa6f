import Mahlo.Correct

/-! 標準形 `isNF` と `Good` の一致、および主定理。

`isNF (Ψ_π(a))` は正規性 `a ∈ C(a, Ψ_π(a))` を `inC a a (Ψ_π a)` で調べる。このとき右側の
`Ψ_π(a)` 自身はまだ正規か分からない（`SemiPsi`：正規性以外の条件だけを満たす）。そこで、
`d = Ψ_π(a)` が `SemiPsi` のとき、`Good` な `x` について

* `cmp x d = .lt → val x < val d`
* `inC x g d = true → val x ∈ C(val g, val d)`
* `baseOf x d = true → Base (val x) (val d)`

が成り立つことを示す（`semi_sound`、`x` の大きさについての帰納法）。これで `isNF ↔ Good`
（`isNF_iff_good`）が出て、主定理 `cmp_correct_of_isNF` が従う。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen MahloOCF

noncomputable section

variable [Setting.{u}]

/-- `Ψ_π(a)` で、正規性以外の `Good` の条件を満たすもの -/
structure SemiPsi (pi a : Tm) : Prop where
  hpi : Good.{u} pi
  ha : Good.{u} a
  hreg : isRegTerm pi = true
  hact : ∀ m d, pi = .Xi m d → val.{u} d < val a

theorem SemiPsi.lt {pi a : Tm} (h : SemiPsi.{u} pi a) : Psi (val.{u} pi) (val a) < val pi := by
  have ihpi := h.hpi.inv
  have hreg := h.hreg
  cases pi with
  | Om c =>
    simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hreg
    cases hreg with
    | inl h0 => subst h0; exact Psi_Om_zero_lt _
    | inr hs =>
      obtain ⟨ζ, hζ, hsΛ⟩ := ihpi.om c rfl hs
      show Psi (Om (val c)) (val a) < Om (val c)
      rw [hζ]
      exact Psi_Om_succ_lt hsΛ _
  | Xi m d => exact Psi_Xi_lt (ihpi.xi m d rfl).1 (ihpi.xi m d rfl).2 (h.hact m d rfl)
  | _ => simp [isRegTerm] at hreg

theorem good_semi {pi a : Tm} (h : Good.{u} (.Psi pi a)) : SemiPsi.{u} pi a := by
  cases h with
  | psi _ _ hpi ha hreg hact _ => exact ⟨hpi, ha, hreg, hact⟩

/-- 主数の項どうしの `cmp` は `cmpP` -/
theorem cmp_principal {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    cmp x y = cmpP x y := by
  rw [cmp, summands_principal hx, summands_principal hy, cmpList]
  cases cmpP x y with
  | eq => show cmpList [] [] = Ordering.eq; rw [cmpList]
  | lt => rfl
  | gt => rfl

/-- `d = Ψ_π(a)`（`SemiPsi`）についての健全性 -/
theorem semi_sound {pi a : Tm} (hs : SemiPsi.{u} pi a) : ∀ (n : Nat) (x : Tm), x.size ≤ n →
    Good.{u} x →
    (isRegTerm x = true → baseOf x (.Psi pi a) = true →
      Base (val.{u} x) (val (Tm.Psi pi a))) ∧
    (cmp x (.Psi pi a) = .lt → val.{u} x < val (Tm.Psi pi a)) ∧
    (∀ g, Good.{u} g → inC x g (.Psi pi a) = true →
      C (val.{u} g) (val (Tm.Psi pi a)) (val x)) := by
  have hψ := hs.lt
  have hRπ := (hs.hpi.inv.reg hs.hreg).isReg
  have hP : IsPrincipal (val.{u} (Tm.Psi pi a)) := Psi_principal_of_lt hRπ.1 hψ
  have hbd := hs.hpi.inv.bounds (ne_zero_of_isRegTerm hs.hreg)
  -- `K_{lev π - 1} < Ψ_π(a) < K_{lev π}`
  have hlow : K (lev pi - 1) < val.{u} (Tm.Psi pi a) := by
    apply (Psi_spec hψ).2 _ (C_K _ _ _)
    cases hbd.2.1 with
    | inl h => exact h
    | inr e => exact absurd e.symm (hRπ.2.2 _)
  have hup : val.{u} (Tm.Psi pi a) < K (lev pi) := lt_trans _ _ _ hψ hbd.2.2
  intro n
  induction n with
  | zero => intro x hx; have := Tm.size_pos x; omega
  | succ n ih =>
    intro x hxs hx
    -- 小さい項については帰納法の仮定
    have ihb := fun y (hy : y.size ≤ n) (gy : Good.{u} y) => (ih y hy gy).1
    have ihc := fun y (hy : y.size ≤ n) (gy : Good.{u} y) => (ih y hy gy).2.1
    have ihi := fun y (hy : y.size ≤ n) (gy : Good.{u} y) => (ih y hy gy).2.2
    -- `baseOf x d`
    have hB : isRegTerm x = true → baseOf x (.Psi pi a) = true →
        Base (val.{u} x) (val (Tm.Psi pi a)) := by
      intro hr hb
      have hx' := hx
      cases hx with
      | om c hc _ =>
        rw [baseOf] at hb
        split at hb
        · rename_i hsc
          obtain ⟨gp, hv⟩ := good_predT hc hsc
          obtain ⟨go, hvo⟩ := good_omOf gp
          have hsz := size_omOf_predT_lt hsc
          simp only [Tm.size] at hsz hxs
          have h1 := ihc _ (by omega) go (beq_iff_eq.mp hb)
          rw [hvo] at h1
          have hcΛ := hc.inv.lt_Λ
          show Base (Om (val c)) _
          rw [hv] at hcΛ ⊢
          exact (base_Om_succ_iff hcΛ).mpr h1
        · rename_i hsc
          have h0 : c = .zero := by
            simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hr
            cases hr with
            | inl h => exact h
            | inr h => exact absurd h hsc
          subst h0
          exact base_Om_zero_iff.mpr (Psi_pos hψ)
      | xi m b _ hb' _ _ =>
        rw [baseOf, Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨gk, hvk⟩ := good_kTerm.{u} (m - 1)
        have hks := kTerm_size (m - 1)
        have := Tm.size_pos b
        simp only [Tm.size] at hxs
        have h1 := ihc _ (by omega) gk hb.1
        rw [hvk] at h1
        have h2 := ihi b (by omega) hb' b hb' hb.2
        exact (base_Xi_iff (hx'.inv.xi m b rfl).1 (hx'.inv.xi m b rfl).2).mpr ⟨h1, h2⟩
      | _ => simp [isRegTerm] at hr
    -- `cmpP x d`（`x` が主数）
    have hPx : isPrincipal x = true → cmpP x (.Psi pi a) = .lt →
        val.{u} x < val (Tm.Psi pi a) := by
      intro hxp hlt
      have ix := hx.inv
      have bx := ix.bounds (ne_zero_of_isPrincipal hxp)
      rw [cmpP.eq_def] at hlt
      by_cases hl : lev x < lev (Tm.Psi pi a)
      · simp only [lev] at hl
        exact lt_of_lt_of_le bx.2.2 (le_trans (K_le (by omega)) (Or.inl hlow))
      by_cases hl' : lev (Tm.Psi pi a) < lev x
      · simp only [hl, hl', ↓reduceIte] at hlt; cases hlt
      simp only [hl, hl', ↓reduceIte] at hlt
      have hlev : lev x = lev pi := by simp only [lev] at hl hl'; omega
      have hx' := hx
      cases hx with
      | zero => simp [isPrincipal] at hxp
      | plus => simp [isPrincipal] at hxp
      | M m _ =>
        simp only [lev] at hlev
        have : K m = K (lev pi - 1) := by rw [← hlev, Nat.add_sub_cancel]
        show K m < _
        rw [this]
        exact hlow
      | om w hw _ =>
        dsimp only at hlt
        rw [cmpOmX.eq_def] at hlt
        simp only [Tm.size] at hxs
        by_cases hf : omegaFixed (Tm.Psi pi a) = true
        · simp only [hf, ↓reduceIte] at hlt
          have h1 := ihc w (by omega) hw hlt
          have hfix : Om (val.{u} (Tm.Psi pi a)) = val (Tm.Psi pi a) := by
            cases pi with
            | Xi m d => exact Psi_fixed hψ (hs.hpi.inv.fixed rfl) hs.hpi.inv.lt_Λ
            | _ => simp [omegaFixed, isXi] at hf
          have h2 := Om_lt_Om h1 (lt_trans _ _ _ hψ hs.hpi.inv.lt_Λ)
          rw [hfix] at h2
          exact h2
        · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hlt
          cases pi with
          | Om c =>
            have hpi' := hs.hpi
            cases hpi' with
            | om _ hc _ =>
              dsimp only at hlt
              split at hlt
              · rename_i h
                rw [cmp_correct hw hc, beq_iff_eq, ocmp_eq_lt_iff] at h
                have hreg := hs.hreg
                simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hreg
                cases hreg with
                | inl h0 => subst h0; exact absurd h (not_lt_zero _)
                | inr hsc =>
                  obtain ⟨ζ, hζ, hsΛ⟩ := hs.hpi.inv.om c rfl hsc
                  have hgt : Om ζ < Psi (Om (val.{u} c)) (val a) := by
                    rw [hζ]; exact Psi_Om_succ_gt hsΛ _
                  rw [hζ] at h
                  exact lt_of_le_of_lt (Om_le_Om (le_of_lt_succ h)
                    (lt_trans _ _ _ (lt_succ_self ζ) hsΛ)) hgt
              · cases hlt
          | Xi _ _ => simp [omegaFixed, isXi] at hf
          | _ => have h := hs.hreg; simp [isRegTerm] at h
      | xi m b _ _ _ _ =>
        dsimp only at hlt
        split at hlt
        · cases hlt
        · rename_i h
          rw [psiLtXi] at h
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
            Classical.not_not] at h
          have hgt := ocmp_eq_gt_iff.mp (by rw [← cmp_correct hs.hpi hx']; exact h.1)
          have hBx := hB rfl (by simpa using h.2)
          have hRT : RegTarget (val.{u} (Tm.Xi m b)) :=
            Or.inr (Or.inr ⟨m, val b, (hx'.inv.xi m b rfl).2, rfl, (hx'.inv.xi m b rfl).1⟩)
          rcases lt_total (val.{u} (Tm.Xi m b)) (val (Tm.Psi pi a)) with h' | h' | h'
          · exact h'
          · exact absurd h'.symm (Psi_ne_regTarget hψ hRT)
          · exact absurd ((Psi_lt_target_iff hψ hRT hgt).mp h') (fun hn => hn hBx)
      | psi sg b hsg hb hreg' _ hnb =>
        dsimp only at hlt
        rw [cmpPsi] at hlt
        have py := hx'.inv.psi sg b rfl
        split at hlt
        · rename_i h
          have e := beq_iff_eq.mp h
          subst e
          rw [cmp_correct hb hs.ha, ocmp_eq_lt_iff] at hlt
          exact Psi_lt_Psi_of_lt hlt py hψ hnb
        rename_i hne
        have hne' : val.{u} sg ≠ val pi := fun e => hne (beq_iff_eq.mpr (val_inj _ _ hsg hs.hpi e))
        split at hlt
        · rename_i h
          have hlt' : val.{u} pi < val sg := by
            rw [cmp_correct hs.hpi hsg, beq_iff_eq, ocmp_eq_lt_iff] at h; exact h
          split at hlt
          · cases hlt
          · rename_i hB'
            have hnB : ¬ Base (val.{u} pi) (val (Tm.Psi sg b)) := fun h' =>
              hB' ((baseOf_correct hs.hpi hs.hreg hx').mpr h')
            exact (Psi_lt_Psi_iff_lt py hψ hlt').mpr hnB
        · rename_i h
          have hlt' : val.{u} sg < val pi := by
            rcases lt_total (val.{u} sg) (val pi) with h' | h' | h'
            · exact h'
            · exact absurd h' hne'
            · exact absurd (by rw [cmp_correct hs.hpi hsg]; exact beq_iff_eq.mpr (ocmp_of_lt h')) h
          split at hlt
          · rename_i hB'
            simp only [Tm.size] at hxs
            have hBs := (ih sg (by omega) hsg).1 hreg' hB'
            exact (Psi_lt_Psi_iff_gt hψ py hlt').mpr hBs
          · cases hlt
    -- `cmp x d`
    have hC : cmp x (.Psi pi a) = .lt → val.{u} x < val (Tm.Psi pi a) := by
      intro hlt
      have hx' := hx
      cases hx with
      | zero => exact Psi_pos hψ
      | plus h r gh gr hhp hr0 _ =>
        rw [cmp, summands_plus, summands_principal (t := .Psi pi a) rfl, cmpList] at hlt
        have hrs : summands r ≠ [] := fun e => hr0 (summands_eq_nil.mp e)
        have hPh : cmpP h (.Psi pi a) = .lt := by
          revert hlt
          cases hcp : cmpP h (.Psi pi a) with
          | lt => intro _; rfl
          | gt => intro hlt; cases hlt
          | eq =>
            intro hlt
            dsimp only at hlt
            cases hsr : summands r with
            | nil => exact absurd hsr hrs
            | cons _ _ => rw [hsr, cmpList] at hlt; cases hlt
        simp only [Tm.size] at hxs
        have h1 := ihc h (by omega) gh (by rw [cmp_principal hhp rfl]; exact hPh)
        have hc := hx'.inv.cnf
        rw [summands_plus, List.map_cons] at hc
        exact hc.lt_of_head_lt hP h1
      | _ =>
        rw [cmp_principal rfl rfl] at hlt
        exact hPx rfl hlt
    refine ⟨hB, hC, ?_⟩
    -- `inC x g d`
    intro g hg hi
    have hx' := hx
    cases hx with
    | zero => exact C_zero _ _
    | M m _ => exact C_K _ _ m
    | plus y z hy hz _ _ _ =>
      rw [inC, Bool.and_eq_true] at hi
      simp only [Tm.size] at hxs
      exact C_add (ihi y (by omega) hy g hg hi.1) (ihi z (by omega) hz g hg hi.2)
    | om w hw _ =>
      rw [inC] at hi
      simp only [Tm.size] at hxs
      exact C_Om hw.inv.lt_Λ (ihi w (by omega) hw g hg hi)
    | xi m b _ hb hcb _ =>
      rw [inC, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hi
      simp only [Tm.size] at hxs
      cases hi with
      | inl h => exact C_lt (hC h)
      | inr h =>
        rw [cmp_correct hb hg, ocmp_eq_lt_iff] at h
        exact C_Xi m h.2 hcb (ihi b (by omega) hb g hg h.1)
    | psi sg b hsg hb hreg' _ hnb =>
      rw [inC, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hi
      simp only [Tm.size] at hxs
      cases hi with
      | inl h => exact C_lt (hC h)
      | inr h =>
        rw [cmp_correct hb hg, ocmp_eq_lt_iff] at h
        exact C_Psi h.2 (hsg.inv.reg hreg').isReg (hx'.inv.psi sg b rfl) hnb
          (ihi sg (by omega) hsg g hg h.1.1) (ihi b (by omega) hb g hg h.1.2)

/-! ### `isNF` と `Good` -/

/-- 標準形の項は `Good` -/
theorem good_of_isNF : ∀ t : Tm, isNF t = true → Good.{u} t := by
  intro t
  induction t with
  | zero => intro _; exact Good.zero
  | M n =>
    intro h
    simp only [isNF, decide_eq_true_eq] at h
    exact Good.M n h
  | plus a b iha ihb =>
    intro h
    simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hap, hb0⟩, hna⟩, hnb⟩, hm⟩ := h
    have ga := iha hna
    have gb := ihb hnb
    refine Good.plus a b ga gb hap hb0 ?_
    intro hd hhd
    cases hs : summands b with
    | nil => rw [hs] at hhd; cases hhd
    | cons h' l =>
      rw [hs] at hhd hm
      simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      simp only [bne_iff_ne, ne_eq] at hm
      have gh := (summands_good b gb h' (by rw [hs]; exact List.mem_cons_self)).1
      rw [cmp_correct gh ga, ocmp_eq_gt_iff] at hm
      exact le_of_not_lt hm
  | Om a iha =>
    intro h
    simp only [isNF, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact Good.om a (iha h.1) h.2
  | Xi n a iha =>
    intro h
    simp only [isNF, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hna⟩, hcap⟩, hC⟩ := h
    have ga := iha hna
    obtain ⟨gs, hvs⟩ := good_succM.{u} hn
    have hcap' : val.{u} a ≤ capK n := by
      simp only [bne_iff_ne, ne_eq] at hcap
      rw [cmp_correct ga gs, ocmp_eq_gt_iff, hvs] at hcap
      exact le_of_not_lt hcap
    exact Good.xi n a hn ga hcap' ((inC_correct ga ga (Good.M n hn)).mp hC)
  | Psi pi a ihpi iha =>
    intro h
    simp only [isNF, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hnpi, hna⟩, hreg⟩, hact⟩, hC⟩ := h
    have gpi := ihpi hnpi
    have ga := iha hna
    have hact' : ∀ m d, pi = .Xi m d → val.{u} d < val a := by
      intro m d e
      subst e
      have gd : Good.{u} d := by cases gpi with | xi _ _ _ hd _ _ => exact hd
      simp only [MahloOCF.lt] at hact
      rw [cmp_correct gd ga, beq_iff_eq, ocmp_eq_lt_iff] at hact
      exact hact
    have hs : SemiPsi.{u} pi a := ⟨gpi, ga, hreg, hact'⟩
    exact Good.psi pi a gpi ga hreg hact' ((semi_sound hs _ a (Nat.le_refl _) ga).2.2 a ga hC)

/-- `Good` な項は標準形 -/
theorem isNF_of_good : ∀ t : Tm, Good.{u} t → isNF t = true := by
  intro t ht
  induction ht with
  | zero => rfl
  | M n hn => simp [isNF, hn]
  | plus a b ha hb hap hb0 hle iha ihb =>
    simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨hap, hb0⟩, iha⟩, ihb⟩, ?_⟩
    cases hs : summands b with
    | nil => exact absurd (summands_eq_nil.mp hs) hb0
    | cons h l =>
      simp only [bne_iff_ne, ne_eq]
      have gh := (summands_good b hb h (by rw [hs]; exact List.mem_cons_self)).1
      rw [cmp_correct gh ha, ocmp_eq_gt_iff]
      exact not_lt_of_le (hle h (by rw [hs]; rfl))
  | om a _ hf iha =>
    simp only [isNF, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨iha, hf⟩
  | xi n a hn ha hcap hC iha =>
    simp only [isNF, Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨gs, hvs⟩ := good_succM.{u} hn
    refine ⟨⟨⟨hn, iha⟩, ?_⟩, (inC_correct ha ha (Good.M n hn)).mpr hC⟩
    simp only [bne_iff_ne, ne_eq]
    rw [cmp_correct ha gs, ocmp_eq_gt_iff, hvs]
    exact not_lt_of_le hcap
  | psi pi a hpi ha hreg hact hn ihpi iha =>
    simp only [isNF, Bool.and_eq_true]
    refine ⟨⟨⟨⟨ihpi, iha⟩, hreg⟩, ?_⟩, ?_⟩
    · cases pi with
      | Xi m d =>
        dsimp only
        have gd : Good.{u} d := by cases hpi with | xi _ _ _ hd _ _ => exact hd
        simp only [MahloOCF.lt]
        rw [cmp_correct gd ha, beq_iff_eq, ocmp_eq_lt_iff]
        exact hact m d rfl
      | _ => rfl
    · exact (inC_correct ha ha (Good.psi pi a hpi ha hreg hact hn)).mpr hn

/-- `isNF` は `Good` のちょうどの判定 -/
theorem isNF_iff_good (t : Tm) : isNF t = true ↔ Good.{u} t :=
  ⟨good_of_isNF t, isNF_of_good t⟩

/-! ### 主定理 -/

/-- 標準形の項について、`cmp` は値の比較と一致する -/
theorem cmp_correct_of_isNF {a b : Tm} (ha : isNF a = true) (hb : isNF b = true) :
    cmp a b = ocmp (val.{u} a) (val b) :=
  cmp_correct (good_of_isNF a ha) (good_of_isNF b hb)

theorem lt_iff_val {a b : Tm} (ha : isNF a = true) (hb : isNF b = true) :
    MahloOCF.lt a b = true ↔ val.{u} a < val b := by
  simp only [MahloOCF.lt]
  rw [cmp_correct_of_isNF ha hb, beq_iff_eq]
  exact ocmp_eq_lt_iff

theorem cmp_eq_iff_val {a b : Tm} (ha : isNF a = true) (hb : isNF b = true) :
    cmp a b = .eq ↔ val.{u} a = val b := by
  rw [cmp_correct_of_isNF ha hb]
  exact ocmp_eq_eq_iff

/-- 標準形の値は一意（`val` は標準形の上で単射） -/
theorem val_inj_of_isNF {a b : Tm} (ha : isNF a = true) (hb : isNF b = true)
    (e : val.{u} a = val b) : a = b :=
  val_inj a b (good_of_isNF a ha) (good_of_isNF b hb) e

/-- 標準形の上で `cmp a b = .eq` なら `a = b` -/
theorem eq_of_cmp_eq {a b : Tm} (ha : isNF a = true) (hb : isNF b = true)
    (h : cmp a b = .eq) : a = b :=
  val_inj_of_isNF.{u} ha hb ((cmp_eq_iff_val.{u} ha hb).mp h)

end

end OCF.Mahlo
