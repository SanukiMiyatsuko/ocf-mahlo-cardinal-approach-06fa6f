import Mahlo.FS.XiFloor

/-! 外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` の場合（`PsiDiagFam`）。

`t = Ψ_π(X)`、`X = pre + R`、`R` の共終数 `σ` が `π` より大きく（`M` でない）、`t < Ψ_σ(X)` でない場合。
`Ψ_σ(X)` は標準形とは限らないので、`σ` の始点 `B = base σ`（標準形）を使う。

* `σ = Ξ_k(e)`（`lev π = lev σ = k`）で、`B` は `π` の底の条件を満たさない（`Ψ_σ(X)` が満たさないので）。
  したがって `B` は全ての `Ψ_π(A)` より小さく、`π` の前線の最大元 `P0` は `B` 以上。
* 列は `t[ν] = Ψ_π(pre ⊕ (c ⊕ R[y_ν]))`、添字 `y` は `P0` の上の `Ξ_k(ξ)`（`ξ < e`）の閉包（`famSeq`）。
  `B ≤ P0 < σ` なので種の仮定（`SeedHyp`）は成り立つ（`e` の加数で `σ` 未満のものは `B` 未満）。
* 共終性：`x = Ψ_π(a) < t` の `a` の `σ` 未満の極大部分項 `f` は `C(a, x)` に入る。`f` は添字の列の下にある
  （`x` 未満なら `π` の下、`x` 以上なら成分に分けて族の閉包・`B` で押さえる）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 列の記述の族 -/

/-- 列の記述の族が共終数の族に一致し、共終数は `S` の元 -/
def FamOK (s : SeqD) (S : List Tm) : Prop :=
  ∀ σ, s.dom = .big σ → s.famOf = (info σ).fam ∧ σ ∈ S

theorem famOK_mono {s : SeqD} {S S' : List Tm} (h : FamOK s S) (hS : ∀ x, x ∈ S → x ∈ S') :
    FamOK s S' := fun σ hd => ⟨(h σ hd).1, hS σ (h σ hd).2⟩

theorem famOK_app {τ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {S : List Tm}
    (h : FamOK r S) : FamOK (.app τ g pre R r P c) S := by
  intro σ hd
  have hd' : r.dom = .big σ := by
    cases hr : r.dom with
    | big σ' =>
      simp only [SeqD.dom, hr] at hd
      split at hd
      · cases hd; rfl
      · cases hd
    | zero => simp [SeqD.dom, hr] at hd
    | one => simp [SeqD.dom, hr] at hd
    | omega => simp [SeqD.dom, hr] at hd
  exact h σ hd'

theorem famOK_shift {s : SeqD} {S : List Tm} (h : FamOK s S) : FamOK (.shift s) S :=
  fun σ hd => h σ hd

theorem famOK_iapp {g : Gen} {pre : List Tm} {r : SeqD} {P c : Tm} {s : SeqD} {S : List Tm}
    (h : FamOK s S) : FamOK (.iapp g pre r P c s) S := by
  intro σ hd
  have hd' : s.dom = .big σ := by
    cases hr : s.dom with
    | big σ' => simp only [SeqD.dom, hr, Cof.big.injEq] at hd; rw [hd]
    | zero => simp [SeqD.dom, hr] at hd
    | one => simp [SeqD.dom, hr] at hd
    | omega => simp [SeqD.dom, hr] at hd
  exact h σ hd'

theorem famOK_tower {G : Tm} {S : List Tm} : FamOK (.tower G) S := by
  intro σ hd; simp [SeqD.dom] at hd

theorem famOK_none {S : List Tm} : FamOK .none S := by
  intro σ hd; simp [SeqD.dom] at hd

theorem splitPosD_mem {τ : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitPosD τ ys = some (pre, R, r)) : (R, r) ∈ ys := by
  unfold splitPosD at h
  split at h
  · cases h
  · rename_i hl
    cases h
    obtain ⟨e, -, -⟩ := dl_split hl
    rw [e]; simp

theorem splitGtD_mem {th : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitGtD th ys = some (pre, R, r)) : (R, r) ∈ ys := by
  unfold splitGtD at h
  split at h
  · cases h
  · rename_i hl
    cases h
    obtain ⟨e, -, -⟩ := dl_split hl
    rw [e]; simp

theorem famOK_lastS {l : DL} {S : List Tm} (h : ∀ p, p ∈ l → FamOK p.2 S) : FamOK (lastS l) S := by
  unfold lastS
  cases e : l.getLast? with
  | none => exact famOK_none
  | some p => exact h p (List.mem_of_getLast? e)

/-- 族の閉包の記述は、加数の記述の族を受け継ぐ -/
theorem famOK_mahloVK (m : Nat) (q ceil : Tm) (P : Option Tm) {S : List Tm}
    (h : ∀ a, a ∈ summands q → FamOK (info a).seq S) : FamOK (mahloVK m q (info q).sums ceil P) S := by
  have hmem : ∀ p, p ∈ (info q).sums → FamOK p.2 S := fun p hp => by
    rw [coh_sums q p hp]
    refine h p.1 ?_
    rw [← info_sums_fst q]
    exact List.mem_map_of_mem hp
  have hlast := famOK_lastS (S := S) hmem
  unfold mahloVK
  dsimp only
  split
  · exact famOK_tower
  split
  · split
    · rename_i pre R r hsp
      split
      · rename_i sq hmk
        obtain ⟨c', rfl⟩ := mkApp_eq_some hmk
        exact famOK_app (hmem (R, r) ((List.dropLast_sublist _).subset (splitPosD_mem hsp)))
      · exact famOK_tower
    · exact famOK_tower
  · split
    · exact famOK_app hlast
    · split
      · exact famOK_app hlast
      · split
        · exact famOK_app (famOK_shift hlast)
        · split
          · rename_i pre R r hsp
            split
            · rename_i sq hmk
              obtain ⟨c', rfl⟩ := mkApp_eq_some hmk
              exact famOK_app (hmem (R, r) (splitGtD_mem hsp))
            · exact famOK_tower
          · exact famOK_tower

theorem famOK_famSeq_info (π ceil : Tm) (P : Option Tm) {S : List Tm}
    (h : ∀ m q, π = .Xi m q → ∀ a, a ∈ summands q → FamOK (info a).seq S) :
    FamOK (famSeq (info π).fam ceil P) S := by
  cases π with
  | Xi m q => exact famOK_mahloVK m q ceil P (h m q rfl)
  | _ => exact famOK_none

/-- 全ての項の列の記述で、共終数が正則項 `σ` なら記述の族は `σ` の族で、`σ` は部分項 -/
theorem famOK_info : ∀ R : Tm, FamOK (info R).seq (subs R) := by
  intro R
  induction R using size_induction with
  | h R ih =>
  cases R with
  | zero => exact famOK_none
  | M n =>
    intro σ hd
    simp only [info, SeqD.dom, Cof.big.injEq] at hd
    subst hd
    exact ⟨rfl, self_mem_subs _⟩
  | plus a b =>
    have hb := ih b (by simp only [Tm.size]; omega)
    exact fun σ hd => ⟨(hb σ hd).1, subs_plus_r (hb σ hd).2⟩
  | Om c =>
    intro σ hd
    by_cases hc : omReg c
    · have e : (info (Om c)).seq = .reg (Om c) (base (Om c)) [] := by rw [info_seq_om, ite_eq_left hc]
      rw [e] at hd ⊢
      simp only [SeqD.dom, Cof.big.injEq] at hd
      subst hd
      exact ⟨rfl, self_mem_subs _⟩
    · have e : (info (Om c)).seq = .om (info c).seq := by rw [info_seq_om, ite_eq_right hc]
      rw [e] at hd ⊢
      have hc' := ih c (by simp only [Tm.size]; omega)
      exact ⟨(hc' σ hd).1, subs_om (hc' σ hd).2⟩
  | Xi m q =>
    intro σ hd
    simp only [info, SeqD.dom, Cof.big.injEq] at hd
    subst hd
    exact ⟨rfl, self_mem_subs _⟩
  | Psi π X =>
    show FamOK (cs π X) (subs (.Psi π X))
    -- 加数の記述
    have hsum : ∀ a, a ∈ summands X → FamOK (info a).seq (subs (.Psi π X)) := fun a ha =>
      famOK_mono (ih a (by
        have := size_le_of_mem_subs (mem_subs_of_mem_summands ha); simp only [Tm.size]; omega))
        (fun x hx => subs_psi_a (subs_trans (mem_subs_of_mem_summands ha) hx))
    have hπq : ∀ m q, π = .Xi m q → ∀ a, a ∈ summands q → FamOK (info a).seq (subs (.Psi π X)) := by
      intro m q e a ha
      subst e
      exact famOK_mono (ih a (by
        have := size_le_of_mem_subs (mem_subs_of_mem_summands ha); simp only [Tm.size]; omega))
        (fun x hx => subs_psi_p (subs_xi (subs_trans (mem_subs_of_mem_summands ha) hx)))
    have hlast : FamOK (lastS (info X).sums) (subs (.Psi π X)) := by
      refine famOK_lastS (fun p hp => ?_)
      rw [coh_sums X p hp]
      refine hsum p.1 ?_
      rw [← info_sums_fst X]
      exact List.mem_map_of_mem hp
    unfold cs cseq
    split
    · split
      · split
        · intro σ hd; simp [SeqD.dom] at hd
        · intro σ hd; simp [SeqD.dom] at hd
      · exact famOK_none
    · split
      · split
        · split
          · exact famOK_famSeq_info _ _ _ hπq
          · intro σ hd; simp [SeqD.dom] at hd
        · exact famOK_famSeq_info _ _ _ hπq
      · unfold limitSeq
        cases hmk : mkApp π (.psi π) (preT (info X).sums) (lastT (info X).sums) (lastS (info X).sums)
            .zero .zero with
        | none => exact famOK_none
        | some s =>
          obtain ⟨c', rfl⟩ := mkApp_eq_some hmk
          simp only [Option.map_some, Option.getD_some]
          simp only [outFix]
          cases hd : (lastS (info X).sums).dom with
          | big σ =>
            cases σ with
            | Xi k e =>
              dsimp only
              split
              · refine famOK_iapp ?_
                obtain ⟨hf, hσs⟩ := hlast (.Xi k e) hd
                rw [hf]
                refine famOK_mahloVK k e _ _ (fun a ha => famOK_mono (ih a ?_) (fun x hx => ?_))
                · have h1 := size_le_of_mem_subs hσs
                  have h2 := size_le_of_mem_subs (mem_subs_of_mem_summands ha)
                  simp only [Tm.size] at h1 h2 ⊢
                  omega
                · exact subs_trans hσs (subs_xi (subs_trans (mem_subs_of_mem_summands ha) hx))
              · exact famOK_app hlast
            | _ => exact famOK_app hlast
          | _ => exact famOK_app hlast

/-! ### 底の条件と始点 -/

/-- 底の条件は上に閉じている（`w` は切断） -/
theorem baseOf_up {π z w : Tm} (hπ : WNF π) (hπT : IsTgt π) (hz : WNF z) (hw : Cut w)
    (hzw : Lt z w) (h : baseOf π z = true) : baseOf π w = true := by
  rcases hπT with rfl | ⟨c, rfl, hs⟩ | ⟨m, d, rfl⟩
  · rw [baseOf_om_zero] at h ⊢
    exact Lt.ne_zero hzw
  · rw [baseOf_om_succ hs] at h ⊢
    exact hw _ _ (wnf_omOf (predT_WNF hπ.om.1 hs)) hz h hzw
  · obtain ⟨hk, hdC⟩ := (baseOf_xi_iff m d z).mp h
    refine (baseOf_xi_iff m d w).mpr ⟨hw _ _ (wnf_kTerm _) hz hk hzw, ?_⟩
    have hdF := hπ.xi.2.1
    exact inC_mono d d z d w hdC (fun v hv hvz => hw _ _ (hdF.of_mem_subs hv) hz hvz hzw)
      (fun _ _ h => h)

/-- 外に足す型の対角化で `t < Ψ_σ(X)` でなければ、`σ = Ξ_k(e)`（`lev π = k`）で、`σ` の始点は `π` の底の
条件を満たさない -/
theorem a2_shape {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R])
    (hns : ¬ isSucc X = true) (hRi : BigInv R σ) (hπσ : Lt π σ) (hσM : ∀ m, σ ≠ .M m)
    (hT : ¬ Lt (.Psi π X) (.Psi σ X)) :
    ∃ k e, σ = .Xi k e ∧ lev π = k ∧ baseOf π (base σ) = false := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hσF := hRi.props.σF
  have hσT := isTgt_of_reg_notM hRi.σreg hσM
  have hX0 : X ≠ .zero := by intro e; rw [e] at hsX; simp [summands] at hsX
  have hlev : lev π = lev σ := by
    rcases Nat.lt_or_eq_of_le (lev_le_of_lt_gen hπσ) with hl | hl
    · exact absurd (lt_of_lev_lt' (by simp only [lev]; exact hl)) hT
    · exact hl
  have hne : π ≠ σ := Lt.ne hπσ
  have hnlt : ¬ Lt σ π := Lt.asymmY hπ hσF hπσ
  have hkey : baseOf π (.Psi σ X) = false := by
    cases e : baseOf π (.Psi σ X) with
    | false => rfl
    | true => exact absurd ((lt_psi_psiY hlev).mpr (Or.inr (Or.inr ⟨hne, hnlt, e⟩))) hT
  -- `σ` の始点は `Ψ_σ(X)` 未満
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRC : inC R X (.Psi π X) = true := inC_of_mem_summands hX hP.Ca hRX
  have hσC : inC σ X (.Psi π X) = true := hRi.σC X _ (Cut.of_wnf ht) hRC
  have hσt : Lt (.Psi π X) σ := lt_transY ht hπ hσF (lt_psi_targetY ht) hπσ
  have hbF := wnf_base hσF hRi.σreg
  have hbT : Lt (base σ) (.Psi σ X) := by
    rcases hσT with rfl | ⟨c, rfl, -⟩ | ⟨m, e, rfl⟩
    · exact lt_psi_psi_same.mpr (zero_lt hX0)
    · exact lt_psi_psi_same.mpr (zero_lt hX0)
    · show Lt (.Psi (.Xi m e) (sc e)) _
      have heX : Lt e X := by
        rcases inC_xi_iff.mp hσC with h | ⟨-, h⟩
        · exact absurd h (Lt.asymmY ht hσF hσt)
        · exact h
      exact lt_psi_psi_same.mpr (succT_lt_of_not_succ hσF.xi.2.1 hX hns heX)
  have hbB : baseOf π (base σ) = false := by
    cases e : baseOf π (base σ) with
    | false => rfl
    | true =>
      rw [baseOf_up hπ hπT hbF (cut_psi hσF hσT hX) hbT e] at hkey; cases hkey
  rcases hσT with rfl | ⟨c, rfl, hs⟩ | ⟨k, e, rfl⟩
  · exact absurd hπσ (not_lt_om_zero_of_reg hπ (IsRegY.tgt hπT))
  · -- `σ = Ω_c`：`π < Ψ_σ(0)` なので `σ` の始点は底の条件を満たす
    exfalso
    have hcF := hσF.om.1
    have hc0 : c ≠ .zero := by intro e; rw [e] at hs; simp [isSucc, summands] at hs
    have hπb : Lt π (base (.Om c)) := by
      show Lt π (.Psi (.Om c) .zero)
      rcases hπT with rfl | ⟨c₁, rfl, -⟩ | ⟨m, d, rfl⟩
      · exact lt_om_psiOmG.mpr (zero_lt hc0)
      · exact lt_om_psiOmG.mpr (lt_om_iffG.mp hπσ)
      · have hOF : IsOF (Tm.Xi m d) := Or.inl ⟨m, d, rfl⟩
        exact (lt_OF_psiOmY hOF hπ hbF).mpr ((lt_OF_omY hOF hπ hcF).mp hπσ)
    have h1 := baseOf_up hπ hπT ht (Cut.of_wnf hbF) (lt_transY ht hπ hbF (lt_psi_targetY ht) hπb)
      (base_selfY ht)
    rw [h1] at hbB; cases hbB
  · exact ⟨k, e, rfl, hlev, hbB⟩

theorem fr_xi_self {m : Nat} {d : Tm} : fr (.Xi m d) (.Xi m d) = fr (.Xi m d) d := by
  show (if Lt (Tm.Xi m d) (.Xi m d) then [Tm.Xi m d] else fr (.Xi m d) d) = _
  rw [ite_eq_right (Lt.irrefl _)]

/-- `σ = Ξ_k(e)` の始点 `B` が `π` の底の条件を満たさなければ、`π` の前線の最大元 `P0` は `B` 以上 -/
theorem a2_P0 {π e : Tm} {k : Nat} (hπ : WNF π) (hπT : IsTgt π) (hlev : lev π = k)
    (hBF : WNF (.Psi (.Xi k e) (sc e))) (hπσ : Lt π (.Xi k e))
    (hnb : baseOf π (.Psi (.Xi k e) (sc e)) = false) :
    ∃ p, maxL (frB π π) = some p ∧ p ∈ fr π π ∧ Le (.Psi (.Xi k e) (sc e)) p := by
  have hσF := hBF.psi.piF
  have hOF : IsOF (Tm.Psi (.Xi k e) (sc e)) := Or.inr ⟨k, e, sc e, rfl⟩
  have hex : ∃ w, w ∈ fr π π ∧ ¬ Lt w (.Psi (.Xi k e) (sc e)) := by
    refine exists_of_not_forall_mem _ (fun hall => ?_)
    rcases hπT with rfl | ⟨c, rfl, hs⟩ | ⟨m, d, rfl⟩
    · rw [(baseOf_om_zero _).mpr (by intro e; cases e)] at hnb; cases hnb
    · have hcF := hπ.om.1
      have hcπ : Lt c (.Om c) := lt_om_selfY hπ
      have hcC : inC c (sc e) (.Psi (.Xi k e) (sc e)) = true :=
        inC_of_fr c (inC_of_ltY _ hcF hπ hcπ) (fun _ _ h => h)
          (fun w hw => inC_of_lt_node (fr_node hw) (hall w hw))
      have hcB := coll_psiY hBF hcF hcC (lt_transY hcF hπ hσF hcπ hπσ)
      have hpB : Lt (predT c) (.Psi (.Xi k e) (sc e)) :=
        lt_transY (predT_WNF hcF hs) hcF hBF (lt_predT hcF hs) hcB
      have : baseOf (.Om c) (.Psi (.Xi k e) (sc e)) = true := by
        rw [baseOf_om_succ hs]
        unfold omOf
        split
        · exact hpB
        · exact (lt_om_OFG hOF hBF).mpr hpB
      rw [this] at hnb; cases hnb
    · have hm : m = k := hlev
      subst hm
      have hdC : inC d d (.Psi (.Xi m e) (sc e)) = true :=
        inC_of_fr d (xi_selfY hπ) (fun _ _ h => h)
          (fun w hw => inC_of_lt_node (fr_node hw) (hall w (by rw [fr_xi_self]; exact hw)))
      have hk := ((baseOf_xi_iff m e _).mp (base_selfY hBF)).1
      have : baseOf (.Xi m d) (.Psi (.Xi m e) (sc e)) = true := (baseOf_xi_iff m d _).mpr ⟨hk, hdC⟩
      rw [this] at hnb; cases hnb
  obtain ⟨w, hw, hwB⟩ := hex
  have hfrF : ∀ x, x ∈ frB π π → WNF x := fun x hx => by
    rw [frB_eq_fr] at hx; exact (fr_elem hπ hx).1
  cases hm : maxL (frB π π) with
  | none =>
    have h0 := maxL_none hm
    rw [frB_eq_fr] at h0
    rw [h0] at hw; cases hw
  | some p =>
    have hpm : p ∈ fr π π := by rw [← frB_eq_fr]; exact maxL_mem hm
    have hwp := maxL_le hfrF hm w (by rw [frB_eq_fr]; exact hw)
    have hwF := (fr_elem hπ hw).1
    exact ⟨p, rfl, hpm, le_transY hBF hwF (fr_elem hπ hpm).1 (le_of_not_ltY hwF hBF hwB) hwp⟩

/-- `σ = Ξ_k(e)` の始点以上で `σ` 未満の種は `SeedHyp` を満たす -/
theorem seedHyp_base {k : Nat} {e p : Tm} (hBF : WNF (.Psi (.Xi k e) (sc e))) (hpF : WNF p)
    (hBp : Le (.Psi (.Xi k e) (sc e)) p) (hpσ : Lt p (.Xi k e)) : SeedHyp k e p := by
  intro L₁ L₂ hsq hL₂ c hc hcσ hce hcT
  have hσF := hBF.psi.piF
  have heF := hσF.xi.2.1
  have hcF := hc.xi.2.1
  have hseF := succT_WNF heF
  have heC : inC e (sc e) (.Psi (.Xi k e) (sc e)) = true := inC_of_succT hBF.psi.Ca
  -- `σ` 未満の `e` の加数は `B` 未満
  have hsumB : ∀ u, u ∈ summands e → Lt u (.Xi k e) → Lt u (.Psi (.Xi k e) (sc e)) :=
    fun u hu hlt => coll_psiY hBF (summands_WNF e heF u hu).1 (inC_of_mem_summands heF heC hu) hlt
  obtain ⟨l', hsc, hl'⟩ := summands_between hcF heF hsq hcT hce
  have hcC : inC c (sc e) (.Psi (.Xi k e) (sc e)) = true := by
    refine (inC_iff_summandsW hcF).mpr (fun u hu => ?_)
    rw [hsc] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact inC_of_mem_summands heF heC (by rw [hsq]; exact List.mem_append_left _ hu)
    · obtain ⟨v, hv, huv⟩ := hl' u hu
      have hve : v ∈ summands e := by rw [hsq]; exact List.mem_append_right _ hv
      have hvF := (summands_WNF e heF v hve).1
      have huF := (summands_WNF c hcF u (by rw [hsc]; exact List.mem_append_right _ hu)).1
      have hvB := hsumB v hve (lt_of_le_of_ltY hvF hpF hσF (hL₂ v hv) hpσ)
      exact inC_of_ltY _ huF hBF (lt_of_le_of_ltY huF hvF hBF huv hvB)
  have hcs : Lt c (sc e) := lt_transY hcF heF hseF hce (lt_succT e)
  have hxC : inC (.Xi k c) (sc e) (.Psi (.Xi k e) (sc e)) = true :=
    inC_xi_iff.mpr (Or.inr ⟨hcC, hcs⟩)
  exact Or.inr (lt_of_lt_of_leY hc hBF hpF (coll_psiY hBF hc hxC hcσ) hBp)

/-- `σ = Ξ_k(e)`（`e` 極限）の素の族の閉包の 0 番目は `σ` の始点未満 -/
theorem s0_first_lt_base {k : Nat} {e : Tm} (hσ : WNF (.Xi k e)) (hBF : WNF (.Psi (.Xi k e) (sc e)))
    (he0 : e ≠ .zero) (hs : ¬ isSucc e = true) (hRinv : ∀ R, R ∈ summands e → Inv R) :
    Lt (SeqD.app (.Xi k e) (.xi k) (preT (info e).sums) (lastT (info e).sums) (lastS (info e).sums)
      .zero .zero).first (.Psi (.Xi k e) (sc e)) := by
  have heF := hσ.xi.2.1
  have hseF := succT_WNF heF
  have heC : inC e (sc e) (.Psi (.Xi k e) (sc e)) = true := inC_of_succT hBF.psi.Ca
  have hσC : inC (.Xi k e) (sc e) (.Psi (.Xi k e) (sc e)) = true :=
    inC_xi_iff.mpr (Or.inr ⟨heC, lt_succT e⟩)
  have hσd : ¬ Lt (.Xi k e) (.Psi (.Xi k e) (sc e)) := Lt.asymmY hBF hσ (lt_psi_targetY hBF)
  have hcut := Cut.of_wnf hBF
  have hse0 : sc e ≠ .zero := by
    intro h0
    have h1 := lt_succT e
    have h2 : Lt e .zero := h0 ▸ h1
    exact not_lt_zero _ h2
  have hvk : mahloVK k e (info e).sums (.Xi k e) none =
      .app (.Xi k e) (.xi k) (preT (info e).sums) (lastT (info e).sums) (lastS (info e).sums)
        .zero .zero := by
    rw [mahloVK, ite_eq_right he0, ite_eq_right hs]
  rw [← hvk]
  unfold SeqD.first
  cases hd : (mahloVK k e (info e).sums (.Xi k e) none).dom with
  | big τ =>
    have F := famBig_mahloVK hσ hRinv (fun p hp => by cases hp) (fun p hp => by cases hp)
      (fun p hp => by cases hp) hd
    have hτF := F.σF
    have hτB : Lt τ (.Psi (.Xi k e) (sc e)) := coll_psiY hBF hτF (F.σC _ _ hcut heC) F.σρ
    have hbτ : inC (base τ) (sc e) (.Psi (.Xi k e) (sc e)) = true :=
      inC_of_ltY _ (wnf_base hτF F.σreg) hBF
        (lt_transY (wnf_base hτF F.σreg) hτF hBF (base_lt hτF F.σreg) hτB)
    have hC := F.ub (sc e) _ .zero hseF hse0 hcut WNF.zero F.pos hbτ hσC hσd
      (fun p hp => by cases hp) (inC_zero _ _)
    exact coll_psiY hBF (F.F .zero WNF.zero F.pos) hC (F.ltρ .zero WNF.zero F.pos)
  | omega =>
    have F := famNat_mahloVK hσ hRinv (fun p hp => by cases hp) (fun p hp => by cases hp)
      (fun p hp => by cases hp) hd
    have hC := F.ub (sc e) _ 0 hseF hse0 hcut hσC hσd (fun p hp => by cases hp)
    exact coll_psiY hBF (F.F 0) hC (F.ltρ 0)
  | zero =>
    rw [hvk] at hd
    exact absurd hd (SeqD.app_dom_ne _ _ _ _ _ _ _).2
  | one =>
    rw [hvk] at hd
    exact absurd hd (SeqD.app_dom_ne _ _ _ _ _ _ _).1

/-! ### 添字の列の下 -/

/-- `lfr` の元の `lfr`（`τ ≤ σ`）は全体の `lfr` の元以下 -/
theorem lfr_of_lfr {σ τ : Tm} (hσ : WNF σ) (hτ : WNF τ) (hτσ : Le τ σ) :
    ∀ {x g f : Tm}, WNF x → g ∈ lfr σ x → f ∈ lfr τ g → ∃ f', f' ∈ lfr τ x ∧ Le f f' := by
  intro x
  induction x using size_induction with
  | h x ih =>
  intro g f hx hg hf
  by_cases hxσ : Lt x σ
  · rw [lfr_of_lt hxσ, List.mem_singleton] at hg
    subst hg
    exact ⟨f, hf, Or.inl rfl⟩
  have hxτ : ¬ Lt x τ := fun h => hxσ (lt_of_lt_of_leY hx hτ hσ h hτσ)
  cases x with
  | zero | M _ => simp only [lfr, hxσ, ↓reduceIte] at hg; cases hg
  | plus a b =>
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rcases (mem_lfr_plus hxσ).mp hg with hg | hg
    · obtain ⟨f', hf', hle⟩ := ih a (by simp only [Tm.size]; omega) ha hg hf
      exact ⟨f', (mem_lfr_plus hxτ).mpr (Or.inl hf'), hle⟩
    · obtain ⟨f', hf', hle⟩ := ih b (by simp only [Tm.size]; omega) hb hg hf
      exact ⟨f', (mem_lfr_plus hxτ).mpr (Or.inr hf'), hle⟩
  | Om a =>
    obtain ⟨f', hf', hle⟩ := ih a (by simp only [Tm.size]; omega) hx.om.1 ((mem_lfr_om hxσ).mp hg) hf
    exact ⟨f', (mem_lfr_om hxτ).mpr hf', hle⟩
  | Xi m a =>
    obtain ⟨f', hf', hle⟩ := ih a (by simp only [Tm.size]; omega) hx.xi.2.1 ((mem_lfr_xi hxσ).mp hg) hf
    exact ⟨f', (mem_lfr_xi hxτ).mpr hf', hle⟩
  | Psi q a =>
    have hP := hx.psi
    rcases (mem_lfr_psi hxσ).mp hg with hg | hg
    · obtain ⟨f', hf', hle⟩ := ih q (by simp only [Tm.size]; omega) hP.piF hg hf
      exact ⟨f', (mem_lfr_psi hxτ).mpr (Or.inl hf'), hle⟩
    · obtain ⟨f', hf', hle⟩ := ih a (by simp only [Tm.size]; omega) hP.aF hg hf
      exact ⟨f', (mem_lfr_psi hxτ).mpr (Or.inr hf'), hle⟩

/-- `e ∉ C(g, z)`（`e ≤ g`、`z < σ = Ξ_k(e)`）なら `z` は `σ` の始点未満 -/
theorem lt_base_of_not_inC {k : Nat} {e z g : Tm} (hσ : WNF (.Xi k e))
    (hBF : WNF (.Psi (.Xi k e) (sc e))) (hz : WNF z) (hzσ : Lt z (.Xi k e)) (hgF : WNF g)
    (heg : Le e g) (hnC : inC e g z = false) : Lt z (.Psi (.Xi k e) (sc e)) := by
  have heF := hσ.xi.2.1
  have hex : ∃ w, w ∈ fr (.Xi k e) e ∧ ¬ Lt w z := by
    refine exists_of_not_forall_mem _ (fun hall => ?_)
    have h := inC_of_fr_lt heF hσ hz heF hgF (xi_selfY hσ) (Or.inr hzσ) heg hall
    rw [h] at hnC; cases hnC
  obtain ⟨w, hw, hwz⟩ := hex
  have hwF := heF.of_mem_subs (fr_spec hw).1
  have heC : inC e (sc e) (.Psi (.Xi k e) (sc e)) = true := inC_of_succT hBF.psi.Ca
  have hwC : inC w (sc e) (.Psi (.Xi k e) (sc e)) = true :=
    (inC_fr e (xi_selfY hσ)
      (fun v hv hvσ hvB => hvσ (lt_transY (heF.of_mem_subs hv) hBF hσ hvB (lt_psi_targetY hBF)))
      (fun v hv hve => lt_transY (heF.of_mem_subs hv) heF (succT_WNF heF) hve (lt_succT e))).mp
      heC w hw
  have hwB := coll_psiY hBF hwF hwC (fr_spec hw).2
  exact lt_of_le_of_ltY hz hwF hBF (le_of_not_ltY hwF hz hwz) hwB

/-- 階 `k` の `M_j`（`lev ≤ k`）は `M_{k-1}` 以下 -/
theorem M_le_floor {k j : Nat} (hM : WNF (.M j)) (hl : lev (Tm.M j) = k) : Le (.M j) (floorLev k) := by
  simp only [lev] at hl
  unfold floorLev kTerm
  rw [ite_eq_right (by have := hM.M; omega)]
  have : j = k - 1 := by omega
  rw [this]; exact Or.inl rfl

/-- 前線が列の下にある `R`（階 `k` 以下）未満の項は列の下（`ω` 型） -/
theorem below_fam_nat {k : Nat} {e : Tm} {P : Option Tm} {y : Nat → Tm} (F : FamNat k e P y)
    (hm : 1 ≤ k) {R : Tm} (hR : WNF R) (hRl : lev R ≤ k) :
    ∀ x, WNF x → Lt x R → (∀ w, w ∈ fr R x → ∃ n, Lt w (y n)) → ∃ n, Lt x (y n) := by
  intro x
  induction x using size_induction with
  | h x ih =>
  intro hx hxR hfr
  have hlev : lev x ≤ k := Nat.le_trans (lev_le_of_lt_gen hxR) hRl
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact ⟨0, lt_y0_of_lev F hm hx hl⟩
  cases x with
  | zero => exfalso; simp only [lev] at hl; omega
  | M j => exact ⟨0, lt_of_le_of_ltY hx (wnf_kTerm _) (F.F 0) (M_le_floor hx hl) F.bot⟩
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hx.plus
    obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hx hR (lt_plus_leftY hx) hxR) (fun w hw => hfr w (fr_mem_plus_l hw))
    exact ⟨n, (lt_plus_prin_iffY hx (F.prin n)).mpr hn⟩
  | Om a =>
    have haF := hx.om.1
    obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) haF
      (lt_transY haF hx hR (lt_om_selfY hx) hxR) (fun w hw => hfr w (fr_mem_om hw))
    exact F.om a n haF hn
  | Xi j a => exact hfr _ (mem_fr_self (Or.inl ⟨j, a, rfl⟩) hxR)
  | Psi q a => exact hfr _ (mem_fr_self (Or.inr ⟨q, a, rfl⟩) hxR)

/-- 前線が `y_ξ` の下にある `R`（階 `k` 以下）未満の項は `y_ξ` の下（正則項型） -/
theorem below_fam_big {k : Nat} {e τ : Tm} {P : Option Tm} {y : Tm → Tm} (F : FamBig k e P τ y)
    (hm : 1 ≤ k) {ξ : Tm} (hξ : WNF ξ) (hξτ : Lt ξ τ) {R : Tm} (hR : WNF R) (hRl : lev R ≤ k) :
    ∀ x, WNF x → Lt x R → (∀ w, w ∈ fr R x → Lt w (y ξ)) → Lt x (y ξ) := by
  have hyF := F.F ξ hξ hξτ
  have hy0F := F.F .zero WNF.zero F.pos
  have hy0 := F.le0 hξ hξτ
  intro x
  induction x using size_induction with
  | h x ih =>
  intro hx hxR hfr
  have hlev : lev x ≤ k := Nat.le_trans (lev_le_of_lt_gen hxR) hRl
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lt_of_leY hx hy0F hyF (lt_y0_of_lev_big F hm hx hl) hy0
  cases x with
  | zero => exfalso; simp only [lev] at hl; omega
  | M j =>
    exact lt_of_lt_of_leY hx hy0F hyF
      (lt_of_le_of_ltY hx (wnf_kTerm _) hy0F (M_le_floor hx hl) F.bot) hy0
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hx.plus
    exact (lt_plus_prin_iffY hx (F.prin ξ)).mpr (ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hx hR (lt_plus_leftY hx) hxR) (fun w hw => hfr w (fr_mem_plus_l hw)))
  | Om a =>
    have haF := hx.om.1
    exact (lt_om_OFG (F.OF ξ) hyF).mpr (ih a (by simp only [Tm.size]; omega) haF
      (lt_transY haF hx hR (lt_om_selfY hx) hxR) (fun w hw => hfr w (fr_mem_om hw)))
  | Xi j a => exact hfr _ (mem_fr_self (Or.inl ⟨j, a, rfl⟩) hxR)
  | Psi q a => exact hfr _ (mem_fr_self (Or.inr ⟨q, a, rfl⟩) hxR)

/-! ### 対角化の文脈 -/

/-- 外に足す型の対角化で `Ψ_σ(X) ≤ t` の場合の文脈：`σ = Ξ_k(e)`、種 `p = P0`、調整 `c` -/
structure A2 (π X R : Tm) (pre : List Tm) (k : Nat) (e p c : Tm) : Prop where
  ht : WNF (.Psi π X)
  hsX : summands X = pre ++ [R]
  hns : ¬ isSucc X = true
  hRd : dom R = .big (.Xi k e)
  hRi : BigInv R (.Xi k e)
  hπσ : Lt π (.Xi k e)
  hlev : lev π = k
  hkey : baseOf π (.Psi (.Xi k e) X) = false
  hnb : baseOf π (.Psi (.Xi k e) (sc e)) = false
  hpm : p ∈ fr π π
  hpmax : maxL (frB π π) = some p
  hBp : Le (.Psi (.Xi k e) (sc e)) p
  hadj : AdjOK π pre R (fundBig R .zero) c
  hcs : cs π X = .iapp (.psi π) pre (info R).seq .zero c (mahloVK k e (info e).sums (.Xi k e) (some p))
  hRinv : ∀ a, a ∈ summands e → Inv a

namespace A2

variable {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm}

theorem hσ (H : A2 π X R pre k e p c) : WNF (.Xi k e) := H.hRi.props.σF
theorem hπ (H : A2 π X R pre k e p c) : WNF π := H.ht.psi.piF
theorem hBF (H : A2 π X R pre k e p c) : WNF (.Psi (.Xi k e) (sc e)) := wnf_base_xi H.hσ
theorem hpF (H : A2 π X R pre k e p c) : WNF p := (fr_elem H.hπ H.hpm).1
theorem hpπ (H : A2 π X R pre k e p c) : Lt p π := (fr_elem H.hπ H.hpm).2.1
theorem hpσ (H : A2 π X R pre k e p c) : Lt p (.Xi k e) := lt_transY H.hpF H.hπ H.hσ H.hpπ H.hπσ
theorem hpmax' (H : A2 π X R pre k e p c) : ∀ w, w ∈ fr π π → Le w p := fun w hw =>
  maxL_le (fun x hx => by rw [frB_eq_fr] at hx; exact (fr_elem H.hπ hx).1) H.hpmax w
    (by rw [frB_eq_fr]; exact hw)

/-- `σ` の始点は全ての `Ψ_π(A)` 未満 -/
theorem hBlt (H : A2 π X R pre k e p c) (A : Tm) : Lt (.Psi (.Xi k e) (sc e)) (.Psi π A) := by
  have hlevσ : lev (Tm.Xi k e) = lev π := by rw [H.hlev]; rfl
  exact (lt_psi_psiY hlevσ).mpr (Or.inr (Or.inl ⟨fun h => Lt.ne H.hπσ h.symm, H.hπσ, H.hnb⟩))

theorem hBπ (H : A2 π X R pre k e p c) : Lt (.Psi (.Xi k e) (sc e)) π :=
  lt_transY H.hBF H.ht H.hπ (H.hBlt X) (lt_psi_targetY H.ht)

theorem heC (H : A2 π X R pre k e p c) : inC e (sc e) (.Psi (.Xi k e) (sc e)) = true :=
  inC_of_succT H.hBF.psi.Ca

/-- `Ψ_σ(b)`（`b < X`）は `t` 未満 -/
theorem psi_σ_lt (H : A2 π X R pre k e p c) {b : Tm} (hb : WNF (.Psi (.Xi k e) b)) (hbX : Lt b X) :
    Lt (.Psi (.Xi k e) b) (.Psi π X) := by
  have hσT : IsTgt (Tm.Xi k e) := Or.inr (Or.inr ⟨k, e, rfl⟩)
  have hlevσ : lev (Tm.Xi k e) = lev π := by rw [H.hlev]; rfl
  have hnbz : baseOf π (.Psi (.Xi k e) b) = false := by
    cases e' : baseOf π (.Psi (.Xi k e) b) with
    | false => rfl
    | true =>
      have h1 := baseOf_up H.hπ H.ht.psi.tgt hb (cut_psi H.hσ hσT H.ht.psi.aF)
        (lt_psi_psi_same.mpr hbX) e'
      have h2 := H.hkey
      rw [h1] at h2; cases h2
  exact (lt_psi_psiY hlevσ).mpr (Or.inr (Or.inl ⟨fun h => Lt.ne H.hπσ h.symm, H.hπσ, hnbz⟩))

/-- `π ≠ Ω_0`（前線が空でない） -/
theorem π_ne (H : A2 π X R pre k e p c) : π ≠ .Om .zero := by
  intro h
  have := H.hpm
  rw [h] at this
  simp [fr] at this

end A2

/-- 族の閉包の列の仕様（`ω` 型） -/
theorem famNat_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    (hdom : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom = .omega) :
    FamNat k e (some p) (fun n => (mahloVK k e (info e).sums (.Xi k e) (some p)).nat n) := by
  have hσ := H.hσ
  have hP : ∀ p', some p = some p' → WNF p' ∧ Lt p' (.Xi k e) ∧ isPrincipal p' = true :=
    fun p' hp' => by cases hp'; exact ⟨H.hpF, H.hpσ, (fr_elem H.hπ H.hpm).2.2.1⟩
  by_cases he0 : e = .zero
  · subst he0; exact famNat_vk_zero hσ hP
  by_cases hs : isSucc e = true
  · exact famNat_vk_succ hσ hs H.hRinv hP hdom
  · exact famNat_vk_lim hσ he0 hs H.hRinv hP
      (fun p' hp' _ _ => by cases hp'; exact seedHyp_base H.hBF H.hpF H.hBp H.hpσ)
      (fun p' hp' he => by
        cases hp'
        exact absurd (he ▸ s0_first_lt_base hσ H.hBF he0 hs H.hRinv) (not_lt_of_leY H.hBF H.hpF H.hBp))
      hdom

/-- 族の閉包の列の仕様（正則項型） -/
theorem famBig_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c τ : Tm} (H : A2 π X R pre k e p c)
    (hdom : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom = .big τ) :
    FamBig k e (some p) τ (fun ξ => (mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ) := by
  have hσ := H.hσ
  have hP : ∀ p', some p = some p' → WNF p' ∧ Lt p' (.Xi k e) ∧ isPrincipal p' = true :=
    fun p' hp' => by cases hp'; exact ⟨H.hpF, H.hpσ, (fr_elem H.hπ H.hpm).2.2.1⟩
  by_cases he0 : e = .zero
  · exfalso
    subst he0
    unfold mahloVK at hdom
    rw [ite_eq_left rfl] at hdom
    exact tower_dom_ne_big _ _ hdom
  by_cases hs : isSucc e = true
  · exact famBig_vk_succ hσ hs H.hRinv hP hdom
  · exact famBig_vk_lim hσ he0 hs H.hRinv hP
      (fun p' hp' _ _ => by cases hp'; exact seedHyp_base H.hBF H.hpF H.hBp H.hpσ)
      (fun p' hp' he => by
        cases hp'
        exact absurd (he ▸ s0_first_lt_base hσ H.hBF he0 hs H.hRinv) (not_lt_of_leY H.hBF H.hpF H.hBp))
      hdom

/-- `π` は族の閉包の列の下（`ω` 型） -/
theorem pi_lt_fam_nat {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    {y : Nat → Tm} (F : FamNat k e (some p) y) : ∃ n, Lt π (y n) := by
  have hπ := H.hπ
  have hσ := H.hσ
  have hm : 1 ≤ k := hσ.xi.1
  have hy0p : Lt p (y 0) := F.seed p rfl
  have hfry : ∀ w, w ∈ fr π π → Lt w (y 0) := fun w hw =>
    lt_of_le_of_ltY (fr_elem hπ hw).1 H.hpF (F.F 0) (H.hpmax' w hw) hy0p
  have hlev := H.hlev
  have hπT := H.ht.psi.tgt
  rcases hπT with rfl | ⟨c₀, rfl, hs⟩ | ⟨m, δ, rfl⟩
  · exact absurd rfl H.π_ne
  · have hcF := hπ.om.1
    obtain ⟨n, hn⟩ := below_fam_nat F hm hπ (Nat.le_of_eq hlev) c₀ hcF (lt_om_selfY hπ)
      (fun w hw => ⟨0, hfry w hw⟩)
    exact F.om c₀ n hcF hn
  · have hmk : m = k := hlev
    subst hmk
    have hδF := hπ.xi.2.1
    have hne : δ ≠ e := fun h => by rw [h] at H; exact Lt.irrefl _ H.hπσ
    rcases (lt_xi_xi0 hne).mp H.hπσ with ⟨hδe, -⟩ | ⟨heδ, hnC⟩
    · refine F.clo δ 0 hπ H.hπσ hδe (fun w hw => ?_)
      have hwπ := k2xY hπ w hw
      have hw' : w ∈ fr (.Xi m δ) δ := fr_subY (WNF.M' hm) hπ (Or.inr (xi_lt_M δ)) hδF hw hwπ
      exact hfry w (by rw [fr_xi_self]; exact hw')
    · exfalso
      have h1 := lt_base_of_not_inC hσ H.hBF hπ H.hπσ hδF (Or.inr heδ) hnC
      exact Lt.asymmY H.hBF hπ H.hBπ h1

/-- 正則項 `τ`（族の閉包の共終数）は `σ` の始点未満 -/
theorem tau_lt_base {π X R : Tm} {pre : List Tm} {k : Nat} {e p c τ : Tm} (H : A2 π X R pre k e p c)
    {y : Tm → Tm} (F : FamBig k e (some p) τ y) : Lt τ (.Psi (.Xi k e) (sc e)) :=
  coll_psiY H.hBF F.σF (F.σC _ _ (Cut.of_wnf H.hBF) H.heC) F.σρ

/-- `π` は族の閉包の列の下（正則項型、`π` の `τ` についての極大部分項が添字未満） -/
theorem pi_lt_fam_big {π X R : Tm} {pre : List Tm} {k : Nat} {e p c τ : Tm} (H : A2 π X R pre k e p c)
    {y : Tm → Tm} (F : FamBig k e (some p) τ y) {ξ : Tm} (hξ : WNF ξ) (hξ0 : Lt .zero ξ) (hξτ : Lt ξ τ)
    (hlfr : ∀ f, f ∈ lfr τ π → Lt f ξ) : Lt π (y ξ) := by
  have hπ := H.hπ
  have hσ := H.hσ
  have hm : 1 ≤ k := hσ.xi.1
  have hyF := F.F ξ hξ hξτ
  have hy0F := F.F .zero WNF.zero F.pos
  have hfry : ∀ w, w ∈ fr π π → Lt w (y ξ) := fun w hw =>
    lt_of_lt_of_leY (fr_elem hπ hw).1 hy0F hyF
      (lt_of_le_of_ltY (fr_elem hπ hw).1 H.hpF hy0F (H.hpmax' w hw) (F.seed p rfl)) (F.le0 hξ hξτ)
  have hτπ : Lt τ π := lt_transY F.σF H.hBF hπ (tau_lt_base H F) H.hBπ
  have hπτ : ¬ Lt π τ := Lt.asymmY F.σF hπ hτπ
  have hlev := H.hlev
  have hπT := H.ht.psi.tgt
  rcases hπT with rfl | ⟨c₀, rfl, hs⟩ | ⟨m, δ, rfl⟩
  · exact absurd rfl H.π_ne
  · have hcF := hπ.om.1
    have h1 := below_fam_big F hm hξ hξτ hπ (Nat.le_of_eq hlev) c₀ hcF (lt_om_selfY hπ) hfry
    exact (lt_om_OFG (F.OF ξ) hyF).mpr h1
  · have hmk : m = k := hlev
    subst hmk
    have hδF := hπ.xi.2.1
    have hne : δ ≠ e := fun h => by rw [h] at H; exact Lt.irrefl _ H.hπσ
    rcases (lt_xi_xi0 hne).mp H.hπσ with ⟨hδe, -⟩ | ⟨heδ, hnC⟩
    · refine F.clo δ ξ hπ H.hπσ hδe hξ hξ0 hξτ (fun f hf => hlfr f ((mem_lfr_xi hπτ).mpr hf))
        (fun w hw => ?_)
      have hwπ := k2xY hπ w hw
      have hw' : w ∈ fr (.Xi m δ) δ := fr_subY (WNF.M' hm) hπ (Or.inr (xi_lt_M δ)) hδF hw hwπ
      exact hfry w (by rw [fr_xi_self]; exact hw')
    · exfalso
      have h1 := lt_base_of_not_inC hσ H.hBF hπ H.hπσ hδF (Or.inr heδ) hnC
      exact Lt.asymmY H.hBF hπ H.hBπ h1

/-! ### 包の元は添字の列の下 -/

/-- `C(g, d)`（`d < t`、`g ≤ X`）の `σ` 未満の元は族の閉包の列の下（`ω` 型） -/
theorem hull_nat {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    {y : Nat → Tm} (F : FamNat k e (some p) y) {g d : Tm} (hg : WNF g) (hd : WNF d)
    (hdt : Lt d (.Psi π X)) (hgX : Le g X) :
    ∀ z, WNF z → Lt z (.Xi k e) → inC z g d = true → ∃ n, Lt z (y n) := by
  have ht := H.ht
  have hX := ht.psi.aF
  have hπ := H.hπ
  have hσ := H.hσ
  have hm : 1 ≤ k := hσ.xi.1
  have heF := hσ.xi.2.1
  have hBF := H.hBF
  have hpF := H.hpF
  have hσT : IsTgt (Tm.Xi k e) := Or.inr (Or.inr ⟨k, e, rfl⟩)
  obtain ⟨n0, hn0⟩ := pi_lt_fam_nat H F
  have hy0p : Lt p (y 0) := F.seed p rfl
  have hBy : ∀ z, WNF z → Lt z (.Psi (.Xi k e) (sc e)) → Lt z (y 0) := fun z hz h =>
    lt_transY hz hpF (F.F 0) (lt_of_lt_of_leY hz hBF hpF h H.hBp) hy0p
  have hty : ∀ z, WNF z → Lt z (.Psi π X) → Lt z (y n0) := fun z hz h =>
    lt_transY hz hπ (F.F n0) (lt_transY hz ht hπ h (lt_psi_targetY ht)) hn0
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hz hzσ hzC
  by_cases hzd : Lt z d
  · exact ⟨n0, hty z hz (lt_transY hz hd ht hzd hdt)⟩
  have hdz : Le d z := le_of_not_ltY hz hd hzd
  have hlev : lev z ≤ k := by have := lev_le_of_lt_gen hzσ; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact ⟨0, lt_y0_of_lev F hm hz hl⟩
  cases z with
  | zero => exfalso; simp only [lev] at hl; omega
  | M j => exact ⟨0, lt_of_le_of_ltY hz (wnf_kTerm _) (F.F 0) (M_le_floor hz hl) F.bot⟩
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hz.plus
    rw [inC_plus, Bool.and_eq_true] at hzC
    obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hz hσ (lt_plus_leftY hz) hzσ) hzC.1
    exact ⟨n, (lt_plus_prin_iffY hz (F.prin n)).mpr hn⟩
  | Om a =>
    have haF := hz.om.1
    rw [inC_om] at hzC
    obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) haF
      (lt_transY haF hz hσ (lt_om_selfY hz) hzσ) hzC
    exact F.om a n haF hn
  | Xi j b =>
    have hj : j = k := hl
    subst hj
    rcases inC_xi_iff.mp hzC with h1 | ⟨hbC, hbg⟩
    · exact absurd h1 hzd
    have hbF := hz.xi.2.1
    have hne : b ≠ e := fun h => by rw [h] at hzσ; exact Lt.irrefl _ hzσ
    rcases (lt_xi_xi0 hne).mp hzσ with ⟨hbe, -⟩ | ⟨heb, hnC⟩
    · have hfrC : ∀ w, w ∈ fr (.M j) b → inC w g d = true := fun w hw => by
        have hw' : w ∈ fr (.Xi j b) b := fr_subY (WNF.M' hm) hz (Or.inr (xi_lt_M b)) hbF hw (k2xY hz w hw)
        exact (inC_fr b (xi_selfY hz)
          (fun v hv hvz hvd => hvz (lt_of_lt_of_leY (hbF.of_mem_subs hv) hd hz hvd hdz))
          (fun v hv hvb => lt_transY (hbF.of_mem_subs hv) hbF hg hvb hbg)).mp hbC w hw'
      obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) F.F F.mono (fr (.M j) b)
        (fun w hw => hbF.of_mem_subs (fr_spec hw).1)
        (fun w hw _ => ih w (by
            have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega)
          (hbF.of_mem_subs (fr_spec hw).1)
          (lt_transY (hbF.of_mem_subs (fr_spec hw).1) hz hσ (k2xY hz w hw) hzσ) (hfrC w hw))
      exact F.clo b N hz hzσ hbe (fun w hw => hN w hw trivial)
    · exact ⟨0, hBy _ hz (lt_base_of_not_inC hσ hBF hz hzσ hbF (Or.inr heb) hnC)⟩
  | Psi κ b =>
    have hQ := hz.psi
    have hκF := hQ.piF
    have hlκ : lev κ = k := hl
    rcases inC_psi_iff.mp hzC with h1 | ⟨hκC, -, hbg⟩
    · exact absurd h1 hzd
    rcases triY hκF hσ with hκσ | hκe | hσκ
    · obtain ⟨n, hn⟩ := ih κ (by simp only [Tm.size]; omega) hκF hκσ hκC
      exact ⟨n, lt_transY hz hκF (F.F n) (lt_psi_targetY hz) hn⟩
    · subst hκe
      exact ⟨n0, hty _ hz (H.psi_σ_lt hz (lt_of_lt_of_leY hQ.aF hg hX hbg hgX))⟩
    · have hlκσ : lev κ = lev (Tm.Xi k e) := hlκ
      have hnb := not_base_of_lt_tgtY hz hσ hσT hlκσ hσκ hzσ
      by_cases hkz : Lt (kTerm (k - 1)) (.Psi κ b)
      · have hnC : inC e e (.Psi κ b) = false := by
          cases h2 : inC e e (.Psi κ b) with
          | false => rfl
          | true => rw [(baseOf_xi_iff k e _).mpr ⟨hkz, h2⟩] at hnb; cases hnb
        exact ⟨0, hBy _ hz (lt_base_of_not_inC hσ hBF hz hzσ heF (Or.inl rfl) hnC)⟩
      · exact ⟨0, lt_of_le_of_ltY hz (wnf_kTerm _) (F.F 0) (le_of_not_ltY (wnf_kTerm _) hz hkz) F.bot⟩

/-- `C(g, d)`（`d < t`、`g ≤ X`）の `σ` 未満の元で `τ` についての極大部分項が `ξ` 未満のものは
`y_ξ` の下（正則項型） -/
theorem hull_big {π X R : Tm} {pre : List Tm} {k : Nat} {e p c τ : Tm} (H : A2 π X R pre k e p c)
    {y : Tm → Tm} (F : FamBig k e (some p) τ y) {ξ : Tm} (hξ : WNF ξ) (hξ0 : Lt .zero ξ)
    (hξτ : Lt ξ τ) (hπy : Lt π (y ξ)) {g d : Tm} (hg : WNF g) (hd : WNF d)
    (hdt : Lt d (.Psi π X)) (hgX : Le g X) :
    ∀ z, WNF z → Lt z (.Xi k e) → inC z g d = true → (∀ f, f ∈ lfr τ z → Lt f ξ) → Lt z (y ξ) := by
  have ht := H.ht
  have hX := ht.psi.aF
  have hπ := H.hπ
  have hσ := H.hσ
  have hm : 1 ≤ k := hσ.xi.1
  have heF := hσ.xi.2.1
  have hBF := H.hBF
  have hpF := H.hpF
  have hτF := F.σF
  have hσT : IsTgt (Tm.Xi k e) := Or.inr (Or.inr ⟨k, e, rfl⟩)
  have hyF := F.F ξ hξ hξτ
  have hy0F := F.F .zero WNF.zero F.pos
  have hy0 := F.le0 hξ hξτ
  have hBy : ∀ z, WNF z → Lt z (.Psi (.Xi k e) (sc e)) → Lt z (y ξ) := fun z hz h =>
    lt_of_lt_of_leY hz hy0F hyF
      (lt_transY hz hpF hy0F (lt_of_lt_of_leY hz hBF hpF h H.hBp) (F.seed p rfl)) hy0
  have hty : ∀ z, WNF z → Lt z (.Psi π X) → Lt z (y ξ) := fun z hz h =>
    lt_transY hz hπ hyF (lt_transY hz ht hπ h (lt_psi_targetY ht)) hπy
  have hτM : Le τ (.M k) :=
    Or.inr (lt_transY hτF hσ (WNF.M' hm) F.σρ (xi_lt_M e))
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hz hzσ hzC hlfr
  by_cases hzτ : Lt z τ
  · exact lt_transY hz hξ hyF (hlfr z (by rw [lfr_of_lt hzτ]; exact List.mem_singleton.mpr rfl))
      (F.ge ξ hξ hξτ)
  by_cases hzd : Lt z d
  · exact hty z hz (lt_transY hz hd ht hzd hdt)
  have hdz : Le d z := le_of_not_ltY hz hd hzd
  have hlev : lev z ≤ k := by have := lev_le_of_lt_gen hzσ; simpa [lev] using this
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lt_of_leY hz hy0F hyF (lt_y0_of_lev_big F hm hz hl) hy0
  cases z with
  | zero => exfalso; simp only [lev] at hl; omega
  | M j =>
    exact lt_of_lt_of_leY hz hy0F hyF
      (lt_of_le_of_ltY hz (wnf_kTerm _) hy0F (M_le_floor hz hl) F.bot) hy0
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hz.plus
    rw [inC_plus, Bool.and_eq_true] at hzC
    exact (lt_plus_prin_iffY hz (F.prin ξ)).mpr (ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hz hσ (lt_plus_leftY hz) hzσ) hzC.1
      (fun f hf => hlfr f ((mem_lfr_plus hzτ).mpr (Or.inl hf))))
  | Om a =>
    have haF := hz.om.1
    rw [inC_om] at hzC
    exact (lt_om_OFG (F.OF ξ) hyF).mpr (ih a (by simp only [Tm.size]; omega) haF
      (lt_transY haF hz hσ (lt_om_selfY hz) hzσ) hzC (fun f hf => hlfr f ((mem_lfr_om hzτ).mpr hf)))
  | Xi j b =>
    have hj : j = k := hl
    subst hj
    rcases inC_xi_iff.mp hzC with h1 | ⟨hbC, hbg⟩
    · exact absurd h1 hzd
    have hbF := hz.xi.2.1
    have hne : b ≠ e := fun h => by rw [h] at hzσ; exact Lt.irrefl _ hzσ
    rcases (lt_xi_xi0 hne).mp hzσ with ⟨hbe, -⟩ | ⟨heb, hnC⟩
    · have hfrC : ∀ w, w ∈ fr (.M j) b → inC w g d = true := fun w hw => by
        have hw' : w ∈ fr (.Xi j b) b := fr_subY (WNF.M' hm) hz (Or.inr (xi_lt_M b)) hbF hw (k2xY hz w hw)
        exact (inC_fr b (xi_selfY hz)
          (fun v hv hvz hvd => hvz (lt_of_lt_of_leY (hbF.of_mem_subs hv) hd hz hvd hdz))
          (fun v hv hvb => lt_transY (hbF.of_mem_subs hv) hbF hg hvb hbg)).mp hbC w hw'
      refine F.clo b ξ hz hzσ hbe hξ hξ0 hξτ (fun f hf => hlfr f ((mem_lfr_xi hzτ).mpr hf))
        (fun w hw => ?_)
      have hwF := hbF.of_mem_subs (fr_spec hw).1
      refine ih w (by have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega) hwF
        (lt_transY hwF hz hσ (k2xY hz w hw) hzσ) (hfrC w hw) (fun f hf => ?_)
      obtain ⟨f', hf', hle⟩ := lfr_of_fr (WNF.M' hm) hτF hτM hbF hw hf
      exact lt_of_le_of_ltY (hwF.of_mem_subs (lfr_spec hf).1) (hbF.of_mem_subs (lfr_spec hf').1) hξ
        hle (hlfr f' ((mem_lfr_xi hzτ).mpr hf'))
    · exact hBy _ hz (lt_base_of_not_inC hσ hBF hz hzσ hbF (Or.inr heb) hnC)
  | Psi κ b =>
    have hQ := hz.psi
    have hκF := hQ.piF
    have hlκ : lev κ = k := hl
    rcases inC_psi_iff.mp hzC with h1 | ⟨hκC, -, hbg⟩
    · exact absurd h1 hzd
    rcases triY hκF hσ with hκσ | hκe | hσκ
    · have h1 := ih κ (by simp only [Tm.size]; omega) hκF hκσ hκC
        (fun f hf => hlfr f ((mem_lfr_psi hzτ).mpr (Or.inl hf)))
      exact lt_transY hz hκF hyF (lt_psi_targetY hz) h1
    · subst hκe
      exact hty _ hz (H.psi_σ_lt hz (lt_of_lt_of_leY hQ.aF hg hX hbg hgX))
    · have hlκσ : lev κ = lev (Tm.Xi k e) := hlκ
      have hnb := not_base_of_lt_tgtY hz hσ hσT hlκσ hσκ hzσ
      by_cases hkz : Lt (kTerm (k - 1)) (.Psi κ b)
      · have hnC : inC e e (.Psi κ b) = false := by
          cases h2 : inC e e (.Psi κ b) with
          | false => rfl
          | true => rw [(baseOf_xi_iff k e _).mpr ⟨hkz, h2⟩] at hnb; cases hnb
        exact hBy _ hz (lt_base_of_not_inC hσ hBF hz hzσ heF (Or.inl rfl) hnC)
      · exact lt_of_lt_of_leY hz hy0F hyF
          (lt_of_le_of_ltY hz (wnf_kTerm _) hy0F (le_of_not_ltY (wnf_kTerm _) hz hkz) F.bot) hy0

/-! ### 共終数 `ω` の場合 -/

namespace A2

variable {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm}

/-- `p < Ψ_π(A)`（前線の元） -/
theorem hpA (H : A2 π X R pre k e p c) (A : Tm) : Lt p (.Psi π A) :=
  sub_lt_psi H.hπ H.ht.psi.tgt A p (fr_elem H.hπ H.hpm).2.2.2.2 (Lt.ne H.hpπ) H.hpF H.hpπ

/-- `t ∈ C(g, d)`（`t ≥ d`）なら `σ` の始点と種 `p` は `C(g, d)` に入り、`σ ∈ C(g, d)` -/
theorem ub_parts (H : A2 π X R pre k e p c) {g d : Tm} (hg : WNF g) (hg0 : g ≠ .zero) (hd : Cut d)
    (hC : inC (.Psi π X) g d = true) (hlt : ¬ Lt (.Psi π X) d) :
    inC (.Xi k e) g d = true ∧ ¬ Lt (.Xi k e) d ∧ inC (.Psi (.Xi k e) (sc e)) g d = true ∧
      inC p g d = true ∧ inC X g d = true ∧ Lt X g := by
  have ht := H.ht
  have hP := ht.psi
  have hX := hP.aF
  have hπ := H.hπ
  have hσ := H.hσ
  have heF := hσ.xi.2.1
  have hRX : R ∈ summands X := by rw [H.hsX]; simp
  rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hXC, hXg⟩
  · exact absurd h1 hlt
  have hσt : Lt (.Psi π X) (.Xi k e) := lt_transY ht hπ hσ (lt_psi_targetY ht) H.hπσ
  have hσCg : inC (.Xi k e) g d = true := H.hRi.σC g d hd (inC_of_mem_summands hX hXC hRX)
  have hσd : ¬ Lt (.Xi k e) d := fun h' => hlt (hd _ _ ht hσ hσt h')
  have heX : Lt e X := by
    have hσC0 := H.hRi.σC X _ (Cut.of_wnf ht) (inC_of_mem_summands hX hP.Ca hRX)
    rcases inC_xi_iff.mp hσC0 with h | ⟨-, h⟩
    · exact absurd h (Lt.asymmY ht hσ hσt)
    · exact h
  have heC : inC e g d = true := by
    rcases inC_xi_iff.mp hσCg with h | ⟨h, -⟩
    · exact absurd h hσd
    · exact h
  have hbC : inC (.Psi (.Xi k e) (sc e)) g d = true :=
    inC_psi_iff.mpr (Or.inr ⟨hσCg, inC_succT (inC_one hg0) heC,
      lt_of_le_of_ltY (succT_WNF heF) hX hg (succT_leY heF hX heX) hXg⟩)
  have hπd : ¬ Lt π d := fun h' => hlt (hd _ _ ht hπ (lt_psi_targetY ht) h')
  exact ⟨hσCg, hσd, hbC, fr_inC_of_tgt hπ hP.tgt hg hd hπC hπd p H.hpm, hXC, hXg⟩

end A2

/-- 共終数 `ω` の場合の列の不変量 -/
theorem natInv_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c : Tm} (H : A2 π X R pre k e p c)
    (hdom : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom = .omega) : NatInv (.Psi π X) := by
  have ht := H.ht
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hsX := H.hsX
  have hRi := H.hRi
  have hRP := hRi.props
  have hσ := H.hσ
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hadj := H.hadj
  have hBF := H.hBF
  have hpF := H.hpF
  have hσM : ∀ m, Tm.Xi k e ≠ .M m := fun m h => by cases h
  have F := famNat_a2 H hdom
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm,
      γ = fun n => (mahloVK k e (info e).sums (.Xi k e) (some p)).nat n := ⟨_, rfl⟩
  have hγn : ∀ n, (mahloVK k e (info e).sums (.Xi k e) (some p)).nat n = γ n := fun n => by
    rw [hγdef]
  rw [← hγdef] at F
  have hγF : ∀ n, WNF (γ n) := F.F
  have hγσ : ∀ n, Lt (γ n) (.Xi k e) := F.ltρ
  have hγm := F.mono
  have hγp : ∀ n, Lt p (γ n) := fun n =>
    lt_of_lt_of_leY hpF (hγF 0) (hγF n) (F.seed p rfl) (F.mono_le (Nat.zero_le n))
  have hBγ : ∀ n, Le (.Psi (.Xi k e) (sc e)) (γ n) := fun n =>
    Or.inr (lt_of_le_of_ltY hBF hpF (hγF n) H.hBp (hγp n))
  have hxF : ∀ n, WNF (fundBig R (γ n)) := fun n => hRP.nf _ (hγF n) (hγσ n)
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := by
    intro n
    rw [fundNat_psi, H.hcs]
    show Tm.Psi π (combine (.psi π) pre c .zero (fundBig R
      ((mahloVK k e (info e).sums (.Xi k e) (some p)).nat n))) = _
    rw [hγn n, combine_psi_zero pre hadj.cF (hxF n)]
  have hcore := fun (n : Nat) => approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF n)
    (hRP.lt _ (hγF n) (hγσ n))
    (fun v hv hne hlt => hRi.gapP hR.2 (γ n) v (hγF n) (hγσ n) hv hne hlt)
    (hRi.pos (γ n) (hγF n) (hγσ n))
  have hAF : ∀ n, WNF (apx pre c (fundBig R (γ n))) := fun n => (hcore n).1
  have hA'F : ∀ n, WNF (oadd c (fundBig R (γ n))) := fun n => wnf_oadd hadj.cF (hxF n)
  have hx0 : ∀ n, fundBig R (γ n) ≠ .zero := fun n => fundBig_ne_zero hRi hσM (hγF n) (hγσ n)
  have hA0 : ∀ n, apx pre c (fundBig R (γ n)) ≠ .zero := fun n e' =>
    hx0 n (oadd_eq_zero hadj.cF (hxF n) (oadd_eq_zero hPF (hA'F n) e').2).2
  have hcutA : ∀ n, Cut (.Psi π (apx pre c (fundBig R (γ n)))) := fun n => cut_psi hπ hπT (hAF n)
  have hσCA : ∀ n, inC (.Xi k e) (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n))))
      = true := fun n => hRi.σC _ _ (hcutA n) ((hcore n).2.2.2.2 R hRX)
  have hσy : ∀ n, ¬ Lt (.Xi k e) (.Psi π (apx pre c (fundBig R (γ n)))) := fun n h' =>
    Lt.asymmY hπ hσ H.hπσ (below_lt_tgt hπ hπT _ hσ h')
  -- 添字は近似の成分
  have hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n))))
      = true := fun n =>
    F.ub _ _ n (hAF n) (hA0 n) (hcutA n) (hσCA n) (hσy n)
      (fun p' hp' => by cases hp'; exact inC_of_lt_cut (hcutA n) _ hpF (H.hpA _))
  have hB : ∀ n, inC (base (.Xi k e)) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true := fun n =>
    inC_of_lt_cut (hcutA n) _ hBF (H.hBlt _)
  -- 上界
  have hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base (.Xi k e)) g d = true ∧ ∀ n, inC (γ n) g d = true := by
    intro g d hg hg0 hd hCt hlt
    obtain ⟨hσCg, hσd, hbC, hpC, -, -⟩ := H.ub_parts hg hg0 hd hCt hlt
    exact ⟨hbC, fun n => F.ub g d n hg hg0 hd hσCg hσd (fun p' hp' => by cases hp'; exact hpC)⟩
  -- 共終性
  have hcof : ∀ a a' N, WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N))))) →
      ∃ m, Lt a' (fundBig R (γ m)) := by
    intro a a' N hxF ha' haX hsa ha'R _
    have haF := hxF.psi.aF
    have hxt : Lt (.Psi π a) (.Psi π X) := lt_psi_psi_same.mpr haX
    have haC : inC a a (.Psi π a) = true := hxF.psi.Ca
    have ha'C : inC a' a (.Psi π a) = true := by
      rw [inC_iff_summandsW ha']
      intro s hs
      exact inC_of_mem_summands haF haC (by rw [hsa]; exact List.mem_append_right _ hs)
    have hxσ : Lt (.Psi π a) (.Xi k e) := lt_transY hxF hπ hσ (lt_psi_targetY hxF) H.hπσ
    have hfC : ∀ f, f ∈ lfr (.Xi k e) a' → inC f a (.Psi π a) = true := fun f hf =>
      inC_lfr hσ hxF (Or.inr hxσ) ha' ha'C hf
    have hull := hull_nat H F haF hxF hxt (Or.inr haX)
    obtain ⟨M, hM⟩ := exists_bound (P := fun _ => True) hγF hγm (lfr (.Xi k e) a')
      (fun f hf => ha'.of_mem_subs (lfr_spec hf).1)
      (fun f hf _ => hull f (ha'.of_mem_subs (lfr_spec hf).1) (lfr_spec hf).2 (hfC f hf))
    have hγ0 : Lt .zero (γ (M + 1)) := zero_lt (fun h0 => by
      have := F.prin (M + 1); rw [h0] at this; cases this)
    refine ⟨M + 1, hRi.lclo a' (γ (M + 1)) ha' ha'R (hγF _) hγ0 (hγσ _) (fun f hf => ?_)⟩
    exact lt_transY (ha'.of_mem_subs (lfr_spec hf).1) (hγF M) (hγF _) (hM f hf trivial) (hγm M)
  -- 2 点の上界
  have hub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d →
      inC (.Psi π (apx pre c (fundBig R (γ (n + 1))))) g d = true →
      ¬ Lt (.Psi π (apx pre c (fundBig R (γ (n + 1))))) d →
      (inC (base (.Xi k e)) g d = true ∨ Le (base (.Xi k e)) (γ n)) ∧ inC (γ n) g d = true := by
    intro g d n hg hg0 hd hCy hlt
    refine ⟨Or.inr (hBγ n), ?_⟩
    rcases inC_psi_iff.mp hCy with h1 | ⟨-, hAC, -⟩
    · exact absurd h1 hlt
    have hcR : Lt (oadd c (fundBig R (γ (n + 1)))) R :=
      oadd_lt_prin hadj.cF (hxF _) hR.2 hadj.cR (hRP.lt _ (hγF _) (hγσ _))
    obtain ⟨-, hyC⟩ := inC_oadd_pre hXn (hA'F (n + 1)) hcR hAC
    have hγ1C := hRi.lo g d (γ (n + 1)) hd (hγF _) (hγσ _)
      (inC_of_oadd_right hadj.cF (hxF _) hyC)
    exact F.ub2 g d n hg hg0 hd hγ1C
  exact natInv_psi_idx' ht hsX hRi hadj γ hγF hγσ hγm hf hC hB hub hcof hub2

/-! ### 共終数が正則項の場合 -/

/-- 共終数が正則項 `τ` の場合の列の不変量 -/
theorem bigInv_a2 {π X R : Tm} {pre : List Tm} {k : Nat} {e p c τ : Tm} (H : A2 π X R pre k e p c)
    (hdom : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom = .big τ) :
    BigInv (.Psi π X) τ := by
  have ht := H.ht
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hsX := H.hsX
  have hRi := H.hRi
  have hRP := hRi.props
  have hσ := H.hσ
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hadj := H.hadj
  have hBF := H.hBF
  have hpF := H.hpF
  have hσM : ∀ m, Tm.Xi k e ≠ .M m := fun m h => by cases h
  have F := famBig_a2 H hdom
  obtain ⟨y, hydef⟩ : ∃ y : Tm → Tm,
      y = fun ξ => (mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ := ⟨_, rfl⟩
  have hyξ : ∀ ξ, (mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ = y ξ := fun ξ => by
    rw [hydef]
  rw [← hydef] at F
  have hτF := F.σF
  have hτ0 := F.pos
  have hτreg := F.σreg
  have hτB := tau_lt_base H F
  have hτσ := F.σρ
  have hbτF := wnf_base hτF hτreg
  have hbτ := base_lt hτF hτreg
  have hyF : ∀ ξ, WNF ξ → Lt ξ τ → WNF (y ξ) := F.F
  have hyσ : ∀ ξ, WNF ξ → Lt ξ τ → Lt (y ξ) (.Xi k e) := F.ltρ
  have hpy : ∀ ξ, WNF ξ → Lt ξ τ → Lt p (y ξ) := fun ξ hξ hξτ =>
    lt_of_lt_of_leY hpF (hyF .zero WNF.zero hτ0) (hyF ξ hξ hξτ) (F.seed p rfl) (F.le0 hξ hξτ)
  have hBy : ∀ ξ, WNF ξ → Lt ξ τ → Le (.Psi (.Xi k e) (sc e)) (y ξ) := fun ξ hξ hξτ =>
    Or.inr (lt_of_le_of_ltY hBF hpF (hyF ξ hξ hξτ) H.hBp (hpy ξ hξ hξτ))
  have hxF : ∀ ξ, WNF ξ → Lt ξ τ → WNF (fundBig R (y ξ)) := fun ξ hξ hξτ =>
    hRP.nf _ (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ)
  have hf : ∀ ξ, WNF ξ → Lt ξ τ →
      fundBig (.Psi π X) ξ = .Psi π (apx pre c (fundBig R (y ξ))) := by
    intro ξ hξ hξτ
    rw [fundBig_psi, H.hcs]
    show Tm.Psi π (combine (.psi π) pre c .zero (fundBig R
      ((mahloVK k e (info e).sums (.Xi k e) (some p)).big ξ))) = _
    rw [hyξ ξ, combine_psi_zero pre hadj.cF (hxF ξ hξ hξτ)]
  have core := fun (ξ : Tm) (hξ : WNF ξ) (hξτ : Lt ξ τ) => approx_core (π := π) ht hsX hadj.cF
    hadj.cR (hxF ξ hξ hξτ) (hRP.lt _ (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ))
    (fun v hv hne hlt => hRi.gapP hR.2 (y ξ) v (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ) hv hne hlt)
    (hRi.pos (y ξ) (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ))
  have hAF : ∀ ξ, WNF ξ → Lt ξ τ → WNF (apx pre c (fundBig R (y ξ))) := fun ξ hξ hξτ =>
    (core ξ hξ hξτ).1
  have hA'F : ∀ ξ, WNF ξ → Lt ξ τ → WNF (oadd c (fundBig R (y ξ))) := fun ξ hξ hξτ =>
    wnf_oadd hadj.cF (hxF ξ hξ hξτ)
  have hx0 : ∀ ξ, WNF ξ → Lt ξ τ → fundBig R (y ξ) ≠ .zero := fun ξ hξ hξτ =>
    fundBig_ne_zero hRi hσM (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ)
  have hA'0 : ∀ ξ, WNF ξ → Lt ξ τ → oadd c (fundBig R (y ξ)) ≠ .zero := fun ξ hξ hξτ e' =>
    hx0 ξ hξ hξτ (oadd_eq_zero hadj.cF (hxF ξ hξ hξτ) e').2
  have hA0 : ∀ ξ, WNF ξ → Lt ξ τ → apx pre c (fundBig R (y ξ)) ≠ .zero := fun ξ hξ hξτ e' =>
    hA'0 ξ hξ hξτ (oadd_eq_zero hPF (hA'F ξ hξ hξτ) e').2
  have hcutA : ∀ ξ, WNF ξ → Lt ξ τ → Cut (.Psi π (apx pre c (fundBig R (y ξ)))) :=
    fun ξ hξ hξτ => cut_psi hπ hπT (hAF ξ hξ hξτ)
  have hτA : ∀ ξ, WNF ξ → Lt ξ τ → Lt τ (.Psi π (apx pre c (fundBig R (y ξ)))) := fun ξ hξ hξτ =>
    hcutA ξ hξ hξτ _ _ hτF hBF hτB (H.hBlt _)
  have hσCA : ∀ ξ, WNF ξ → Lt ξ τ → inC (.Xi k e) (apx pre c (fundBig R (y ξ)))
      (.Psi π (apx pre c (fundBig R (y ξ)))) = true := fun ξ hξ hξτ =>
    hRi.σC _ _ (hcutA ξ hξ hξτ) ((core ξ hξ hξτ).2.2.2.2 R hRX)
  have hσy : ∀ ξ, ¬ Lt (.Xi k e) (.Psi π (apx pre c (fundBig R (y ξ)))) := fun ξ h' =>
    Lt.asymmY hπ hσ H.hπσ (below_lt_tgt hπ hπT _ hσ h')
  have hyC : ∀ ξ, WNF ξ → Lt ξ τ → inC (y ξ) (apx pre c (fundBig R (y ξ)))
      (.Psi π (apx pre c (fundBig R (y ξ)))) = true := fun ξ hξ hξτ =>
    F.ub _ _ ξ (hAF ξ hξ hξτ) (hA0 ξ hξ hξτ) (hcutA ξ hξ hξτ) hξ hξτ
      (inC_of_lt_cut (hcutA ξ hξ hξτ) _ hbτF (hcutA ξ hξ hξτ _ _ hbτF hτF hbτ (hτA ξ hξ hξτ)))
      (hσCA ξ hξ hξτ) (hσy ξ)
      (fun p' hp' => by cases hp'; exact inC_of_lt_cut (hcutA ξ hξ hξτ) _ hpF (H.hpA _))
      (inC_of_lt_cut (hcutA ξ hξ hξτ) _ hξ (hcutA ξ hξ hξτ _ _ hξ hτF hξτ (hτA ξ hξ hξτ)))
  have hyF' : ∀ ξ, WNF ξ → Lt ξ τ → WNF (.Psi π (apx pre c (fundBig R (y ξ)))) := fun ξ hξ hξτ =>
    approx_nf ht hsX hRi hadj (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ) (hyC ξ hξ hξτ)
      (inC_of_lt_cut (hcutA ξ hξ hξτ) _ hBF (H.hBlt _))
  have hAlt : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η τ →
      Lt (apx pre c (fundBig R (y ξ))) (apx pre c (fundBig R (y η))) := by
    intro ξ η hξ hη hξη hητ
    have hξτ := lt_transY hξ hη hτF hξη hητ
    exact oadd_lt_oadd hPF (hA'F ξ hξ hξτ) (hA'F η hη hητ)
      (oadd_lt_oadd hadj.cF (hxF ξ hξ hξτ) (hxF η hη hητ)
        (hRP.mono _ _ (hyF ξ hξ hξτ) (hyF η hη hητ) (F.mono ξ η hξ hη hξη hητ) (hyσ η hη hητ)))
  have hτt : Lt τ (.Psi π X) := lt_transY hτF hBF ht hτB (H.hBlt X)
  -- 添字での共終性
  have hcloS : ∀ β, WNF β → Lt .zero β → Lt β τ → ∀ x, WNF x → Lt x (.Psi π X) →
      (∀ f, f ∈ lfr τ x → Lt f β) → Lt x (.Psi π (apx pre c (fundBig R (y β)))) := by
    intro β hβ hβ0 hβτ x
    induction x using size_induction with
    | h x ih =>
    intro hx hxt hfr
    have hyβ := hyF' β hβ hβτ
    by_cases hxτ : Lt x τ
    · have h1 := hfr x (by rw [lfr_of_lt hxτ]; exact List.mem_singleton.mpr rfl)
      exact lt_transY hx hβ hyβ h1 (lt_transY hβ hτF hyβ hβτ (hτA β hβ hβτ))
    refine psi_step ht hyβ hx hxt (fun w hw => ?_) (fun ρ a e' hρt => ?_) (fun a e' => ?_)
    · have hwx := parF_lt hx hw
      have hwF := hx.of_mem_subs (parF_mem_subs hw)
      refine ih w (parL_sub (parF_sub_parL hw)).2 hwF (lt_transY hwF hx ht hwx hxt) (fun f hf => ?_)
      obtain ⟨g, hg, hfg⟩ := lfr_of_parF hτF hx hxτ hw hf
      exact lt_of_le_of_ltY (hwF.of_mem_subs (lfr_spec hf).1) (hx.of_mem_subs (lfr_spec hg).1)
        hβ hfg (hfr g hg)
    · subst e'
      exact ih ρ (by simp only [Tm.size]; omega) hx.psi.piF hρt
        (fun f hf => hfr f ((mem_lfr_psi hxτ).mpr (Or.inl hf)))
    · subst e'
      have haF := hx.psi.aF
      have haX : Lt a X := lt_psi_psi_same.mp hxt
      have hxβF := hxF β hβ hβτ
      rcases lt_split hX hsX haF haX with hle | ⟨a', ha', ha'0, ha'R, hsa, hae⟩
      · exact lt_of_le_of_ltY haF hPF (hAF β hβ hβτ) hle
          (lt_oadd_left hPF (hA'F β hβ hβτ) (hA'0 β hβ hβτ))
      · rw [hae]
        have hπy : Lt π (y β) := pi_lt_fam_big H F hβ hβ0 hβτ
          (fun f hf => hfr f ((mem_lfr_psi hxτ).mpr (Or.inl hf)))
        have haC : inC a a (.Psi π a) = true := hx.psi.Ca
        have ha'C : inC a' a (.Psi π a) = true := by
          rw [inC_iff_summandsW ha']
          intro s hs
          exact inC_of_mem_summands haF haC (by rw [hsa]; exact List.mem_append_right _ hs)
        have hxσ : Lt (.Psi π a) (.Xi k e) := lt_transY hx hπ hσ (lt_psi_targetY hx) H.hπσ
        have hull := hull_big H F hβ hβ0 hβτ hπy haF hx hxt (Or.inr haX)
        have hlfrσ : ∀ f, f ∈ lfr (.Xi k e) a' → Lt f (y β) := by
          intro f hf
          have hfF := ha'.of_mem_subs (lfr_spec hf).1
          refine hull f hfF (lfr_spec hf).2 (inC_lfr hσ hx (Or.inr hxσ) ha' ha'C hf) (fun g hg => ?_)
          obtain ⟨g', hg', hgg'⟩ := lfr_of_lfr hσ hτF (Or.inr hτσ) ha' hf hg
          obtain ⟨g'', hg'', hg'g''⟩ := lfr_suffix hτF pre haF ha' ha'0 hsa hg'
          have hgF := hfF.of_mem_subs (lfr_spec hg).1
          have hg'F := ha'.of_mem_subs (lfr_spec hg').1
          have hg''F := haF.of_mem_subs (lfr_spec hg'').1
          exact lt_of_le_of_ltY hgF hg''F hβ (le_transY hgF hg'F hg''F hgg' hg'g'')
            (hfr g'' ((mem_lfr_psi hxτ).mpr (Or.inr hg'')))
        have h1 := hRi.lclo a' (y β) ha' ha'R (hyF β hβ hβτ) (zero_lt (F.ne_zero β))
          (hyσ β hβ hβτ) hlfrσ
        exact oadd_lt_oadd hPF ha' (hA'F β hβ hβτ)
          (lt_of_lt_of_leY ha' hxβF (hA'F β hβ hβτ) h1 (le_oadd_right hadj.cF hxβF))
  refine {
    props := ⟨hτF, hτ0, fun ξ hξ hξτ => ?_, fun ξ hξ hξτ => ?_,
      fun ξ η hξ hη hξη hητ => ?_, fun x hx hxt => ?_⟩
    σreg := hτreg
    σsub := subs_psi_a (subs_trans (mem_subs_of_mem_summands hRX)
      (subs_trans hRi.σsub (subs_xi F.σsub)))
    σle := Or.inr hτt
    pos := fun ξ hξ hξτ h0 => by rw [hf ξ hξ hξτ] at h0; cases h0
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξτ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξτ hC => ?_
    ge := fun ξ hξ hξτ => by
      rw [hf ξ hξ hξτ]
      exact Or.inr (hcutA ξ hξ hξτ _ _ hξ hτF hξτ (hτA ξ hξ hξτ))
    gap := fun ξ v hξ hξτ hv hne hvt => by
      rw [hf ξ hξ hξτ]
      exact Or.inr (approx_gap ht (core ξ hξ hξτ).2.2.1 (core ξ hξ hξτ).2.2.2.1 v hv hne hvt)
    gapP := fun _ ξ v hξ hξτ hv hne hvt => by
      rw [hf ξ hξ hξτ]
      exact approx_gap ht (core ξ hξ hξτ).2.2.1 (core ξ hξ hξτ).2.2.2.1 v hv hne hvt
    lclo := fun x β hx hxt hβ hβ0 hβτ hfr => by
      rw [hf β hβ hβτ]; exact hcloS β hβ hβ0 hβτ x hx hxt hfr
    nsucc := fun ξ hξ hξτ _ _ => by
      rw [hf ξ hξ hξτ]
      intro he
      have hπ0 : π = .Om .zero := by simp [isSucc, summands, one] at he; exact he.1
      exact H.π_ne hπ0
    bge := fun ξ hξ hξτ => by
      rw [hf ξ hξ hξτ]
      exact Or.inr (hcutA ξ hξ hξτ _ _ hbτF hτF hbτ (hτA ξ hξ hξτ))
    lbK := fun m' e' _ ξ hξ hξτ => by
      rw [hf ξ hξ hξτ, ← e']
      exact Or.inr (hτA ξ hξ hξτ)
    lbS := fun m' e' hlt ξ hξ hξτ => by
      rw [hf ξ hξ hξτ]
      have hm' : 1 ≤ m' := by have h := hτF; rw [e'] at h; exact h.M
      exact Or.inr (below_transfer hπ hπT (succM m') (WNF.succM hm')
        (fun Y hY _ => absurd (psi_mem_subs_succM hY) H.π_ne) hlt)
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hητ hbC hξC hC => by
      have hξτ := lt_transY hξ hη hτF hξη hητ
      rw [hf η hη hητ] at hC
      rw [hf ξ hξ hξτ]
      exact approx_ub2 ht hsX hadj (hxF ξ hξ hξτ) (hxF η hη hητ)
        (hRP.lt _ (hyF η hη hητ) (hyσ η hη hητ))
        (hRP.mono _ _ (hyF ξ hξ hξτ) (hyF η hη hητ) (F.mono ξ η hξ hη hξη hητ) (hyσ η hη hητ))
        (hyF' ξ hξ hξτ) (hyF' η hη hητ) hg hg0 hd hC
        (fun hxC => hRi.ub2 g d (y ξ) (y η) hg hg0 hd (hyF ξ hξ hξτ) (hyF η hη hητ)
          (F.mono ξ η hξ hη hξη hητ) (hyσ η hη hητ) (Or.inr (hBy ξ hξ hξτ))
          (F.ub2 g d ξ η hg hg0 hd hξ hη hξη hητ hbC hξC
            (hRi.lo g d (y η) hd (hyF η hη hητ) (hyσ η hη hητ) hxC)) hxC)
    bw := fun g d ξ L hd hξ hξτ hL hτL hC => by
      rw [hf ξ hξ hξτ] at hC
      rcases inC_psi_iff.mp hC with h1 | ⟨-, hAC, -⟩
      · exact ⟨base τ, hbτF, inC_of_lt_cut hd g hbτF (hd _ _ hbτF (hyF' ξ hξ hξτ)
          (hcutA ξ hξ hξτ _ _ hbτF hτF hbτ (hτA ξ hξ hξτ)) h1), Or.inl rfl,
          lt_transY hbτF hτF hL hbτ hτL⟩
      · exact F.bw g d ξ L hd hξ hξτ hL hτL (hRi.lo g d (y ξ) hd (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ)
          (inC_of_oadd_right hadj.cF (hxF ξ hξ hξτ)
            (inC_of_oadd_right hPF (hA'F ξ hξ hξτ) hAC))) }
  · rw [hf ξ hξ hξτ]; exact hyF' ξ hξ hξτ
  · rw [hf ξ hξ hξτ]; exact lt_psi_psi_same.mpr (core ξ hξ hξτ).2.1
  · rw [hf ξ hξ (lt_transY hξ hη hτF hξη hητ), hf η hη hητ]
    exact lt_psi_psi_same.mpr (hAlt ξ η hξ hη hξη hητ)
  · obtain ⟨ξ, hξ, hξ0, hξτ, hl⟩ := exists_above hτF hτreg hτ0 (lfr τ x)
      (fun f hf => ⟨hx.of_mem_subs (lfr_spec hf).1, (lfr_spec hf).2⟩)
    exact ⟨ξ, hξ, hξτ, by rw [hf ξ hξ hξτ]; exact Or.inr (hcloS ξ hξ hξ0 hξτ x hx hxt hl)⟩
  · by_cases hlt : Lt (.Psi π X) d
    · exact inC_of_lt_cut hd g hτF (hd _ _ hτF ht hτt hlt)
    rcases inC_psi_iff.mp hC with h1 | ⟨-, hXC, -⟩
    · exact absurd h1 hlt
    have hσCg := hRi.σC g d hd (inC_of_mem_summands hX hXC hRX)
    by_cases hσd : Lt (.Xi k e) d
    · exact inC_of_lt_cut hd g hτF (hd _ _ hτF hσ hτσ hσd)
    rcases inC_xi_iff.mp hσCg with h | ⟨heC, -⟩
    · exact absurd h hσd
    · exact F.σC g d hd heC
  · rw [hf ξ hξ hξτ]
    by_cases hlt : Lt (.Psi π X) d
    · exact inC_of_lt_cut hd g (hyF' ξ hξ hξτ) (hd _ _ (hyF' ξ hξ hξτ) ht
        (lt_psi_psi_same.mpr (core ξ hξ hξτ).2.1) hlt)
    obtain ⟨hσCg, hσd, hbσC, hpC, -, -⟩ := H.ub_parts hg hg0 hd hC hlt
    have hyCg := F.ub g d ξ hg hg0 hd hξ hξτ hbC hσCg hσd
      (fun p' hp' => by cases hp'; exact hpC) hξC
    exact approx_ub ht hsX hadj (hxF ξ hξ hξτ) (hyF' ξ hξ hξτ) (core ξ hξ hξτ).2.1 hg hg0 hd hC
      (fun hRC => hRi.ub g d (y ξ) hg hg0 hd (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ) hbσC hRC hyCg)
  · rw [hf ξ hξ hξτ] at hC
    rcases inC_psi_iff.mp hC with h1 | ⟨-, hAC, -⟩
    · have hξy : Lt ξ (.Psi π (apx pre c (fundBig R (y ξ)))) :=
        hcutA ξ hξ hξτ _ _ hξ hτF hξτ (hτA ξ hξ hξτ)
      exact inC_of_lt_cut hd g hξ (hd _ _ hξ (hyF' ξ hξ hξτ) hξy h1)
    · exact F.lo g d ξ hd hξ hξτ (hRi.lo g d (y ξ) hd (hyF ξ hξ hξτ) (hyσ ξ hξ hξτ)
        (inC_of_oadd_right hadj.cF (hxF ξ hξ hξτ) (inC_of_oadd_right hPF (hA'F ξ hξ hξτ) hAC)))

/-! ### まとめ -/

/-- 族の閉包の記述の共終数は `0`・後者でない -/
theorem mahloVK_dom_ne (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    (mahloVK m q qs ceil P).dom ≠ .zero ∧ (mahloVK m q qs ceil P).dom ≠ .one := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨(SeqD.app_dom_ne _ _ _ _ _ _ _).2, (SeqD.app_dom_ne _ _ _ _ _ _ _).1⟩
    | (obtain ⟨c', rfl⟩ := mkApp_eq_some (by assumption)
       exact ⟨(SeqD.app_dom_ne _ _ _ _ _ _ _).2, (SeqD.app_dom_ne _ _ _ _ _ _ _).1⟩)
    | (constructor <;> simp [SeqD.dom])

/-- 外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` の場合の列の不変量 -/
theorem psiDiagFam_proof : PsiDiagFam := by
  intro π X R σ pre ht hsX hns hRd hRi hπσ hσM hT ih
  obtain ⟨k, e, rfl, hlev, hnb⟩ := a2_shape ht hsX hns hRi hπσ hσM hT
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hσF := hRi.props.σF
  have hlevσ : lev π = lev (Tm.Xi k e) := hlev
  have hkey : baseOf π (.Psi (.Xi k e) X) = false := by
    cases h : baseOf π (.Psi (.Xi k e) X) with
    | false => rfl
    | true =>
      exact absurd ((lt_psi_psiY hlevσ).mpr
        (Or.inr (Or.inr ⟨Lt.ne hπσ, Lt.asymmY hπ hσF hπσ, h⟩))) hT
  have hBF : WNF (.Psi (.Xi k e) (sc e)) := wnf_base_xi hσF
  obtain ⟨p, hpmax, hpm, hBp⟩ := a2_P0 hπ hπT hlev hBF hπσ hnb
  -- 列の記述
  have hr : (info R).seq.dom = .big (.Xi k e) := hRd
  have hk : kAdj π π (.psi π) pre R (info R).seq = .zero := by unfold kAdj; rw [hr]
  have hfirst : (info R).seq.first = fundBig R .zero := by unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns hk
    (by rw [hfirst]; exact hRi.props.nf .zero WNF.zero hRi.props.pos)
  rw [hfirst] at hadj
  have hXe : X = oadd (ofSummands pre) R := eq_oadd_of_summands hX hsX
  have hσne : Tm.Xi k e ≠ π := fun h => Lt.ne hπσ h.symm
  have hTt : ltB (.Psi (.Xi k e) (oadd (ofSummands pre) R)) (.Psi π (oadd (ofSummands pre) R))
      = true := by
    rw [← hXe]
    exact ltB_iff.mpr ((lt_psi_psiY hlevσ.symm).mpr (Or.inr (Or.inl ⟨hσne, hπσ, hkey⟩)))
  have hσπB : ltB (.Xi k e) π = false := by
    cases h : ltB (.Xi k e) π with
    | false => rfl
    | true => exact absurd (ltB_iff.mp h) (Lt.asymmY hπ hσF hπσ)
  have hfam := (famOK_info R (.Xi k e) hr).1
  have hout : outsideMode π (.Xi k e) (.psi π) pre R = true := outsideMode_ne hσM hσne pre R
  have hcs : cs π X = .iapp (.psi π) pre (info R).seq .zero c
      (mahloVK k e (info e).sums (.Xi k e) (some p)) := by
    rw [cs_lim_eq hX hsX hns, hmk, Option.map_some, Option.getD_some]
    simp only [outFix, hr, hσπB, hout, hTt, Bool.not_false, Bool.and_self, ↓reduceIte]
    rw [hfam, hpmax]
    rfl
  have hRinv : ∀ a, a ∈ summands e → Inv a := by
    intro a ha
    refine ih a ?_ (summands_WNF e hσF.xi.2.1 a ha).1
    have hRX : R ∈ summands X := by rw [hsX]; simp
    have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands ha)
    have h2 := size_le_of_mem_subs hRi.σsub
    have h3 := size_le_of_mem_subs (mem_subs_of_mem_summands hRX)
    simp only [Tm.size] at h1 h2 h3 ⊢
    omega
  have H : A2 π X R pre k e p c :=
    ⟨ht, hsX, hns, hRd, hRi, hπσ, hlev, hkey, hnb, hpm, hpmax, hBp, hadj, hcs, hRinv⟩
  have hdt : dom (.Psi π X) = (SeqD.iapp (.psi π) pre (info R).seq .zero c
      (mahloVK k e (info e).sums (.Xi k e) (some p))).dom := by rw [dom_psi, hcs]
  obtain ⟨hne0, hne1⟩ := mahloVK_dom_ne k e (info e).sums (.Xi k e) (some p)
  refine ⟨fun hd => ?_, fun τ hd => ?_⟩
  · rw [hdt] at hd
    cases hs : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom with
    | omega => exact natInv_a2 H hs
    | big τ' => simp [SeqD.dom, hs] at hd
    | zero => exact absurd hs hne0
    | one => exact absurd hs hne1
  · rw [hdt] at hd
    cases hs : (mahloVK k e (info e).sums (.Xi k e) (some p)).dom with
    | big τ' =>
      simp only [SeqD.dom, hs, Cof.big.injEq] at hd
      subst hd
      exact bigInv_a2 H hs
    | omega => simp [SeqD.dom, hs] at hd
    | zero => exact absurd hs hne0
    | one => exact absurd hs hne1

end MahloOCF.FS
