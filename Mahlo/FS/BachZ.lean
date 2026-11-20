import Mahlo.FS.BachLift

/-! 崩壊の 0 番目の形。

極限の引数 `X = pre + R` の崩壊 `Ψ_π(X)` の 0 番目は `Ψ_π(pre ⊕ (c ⊕ x))`（`c` は調整、`x` は `R` の列の
添字 `γ ≥ 0` の項なので `x ≥ R[0]`）（`psi_lim_f0`）。対角化（素・`M_m`・外に足す型・族の閉包）を含む全ての
場合で成り立つ。 -/

namespace MahloOCF.FS

open Tm

/-! ### 補題 -/

theorem bigProps_mono_le {t σ : Tm} (h : BigProps t σ) {ξ η : Tm} (hξ : WNF ξ) (hη : WNF η)
    (hξη : Le ξ η) (hησ : Lt η σ) : Le (fundBig t ξ) (fundBig t η) := by
  rcases hξη with rfl | hlt
  · exact Or.inl rfl
  · exact Or.inr (h.mono ξ η hξ hη hlt hησ)

/-- 調整の形：`0`（下限が `pre` で始まらない）か `rt + 1`（下限 `δ = pre ⊕ rt`） -/
def AdjShape (π : Tm) (pre : List Tm) (c : Tm) : Prop :=
  (c = .zero ∧ tailRaw (argR? π) pre = none) ∨ ∃ rt, tailRaw (argR? π) pre = some rt ∧ c = sc rt

/-- `mkApp` の作る `app` の調整は標準形で、`0` か `rt + 1` -/
theorem mkApp_psi_wnf {π : Tm} {pre : List Tm} {R : Tm} {r s : SeqD} (hπ : WNF π)
    (h : mkApp π (.psi π) pre R r .zero .zero = some s) :
    ∃ c, s = .app π (.psi π) pre R r .zero c ∧ WNF c ∧ AdjShape π pre c := by
  unfold mkApp at h
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?] at h
  split at h
  · rename_i hrt
    cases h; exact ⟨_, rfl, WNF.zero, Or.inl ⟨rfl, hrt⟩⟩
  · rename_i rt hrt
    split at h
    · cases h
    · cases h
      refine ⟨_, rfl, succT_WNF ?_, Or.inr ⟨rt, hrt, rfl⟩⟩
      cases hδ : argR? π with
      | none => rw [hδ] at hrt; simp [tailRaw] at hrt
      | some δ => rw [hδ] at hrt; exact wnf_tailRaw (wnf_argR hπ hδ) hrt

/-- 対角化の添字の 0 番目（ψ への崩壊、種 `0`）：`0`・外に足す型（`σ` が `M` でない、`σ ≠ τ`）・`kTop` -/
theorem gam0_psi_cases (τ σ : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (c : Tm) :
    gam τ σ (.psi τ) pre R r c .zero 0 = .zero ∨ ((∀ m, σ ≠ .M m) ∧ σ ≠ τ) ∨
      ∃ m, σ = .M m ∧ gam τ σ (.psi τ) pre R r c .zero 0 = kTop τ m pre R r := by
  simp only [gam]
  split
  · cases σ with
    | M m => exact Or.inr (Or.inr ⟨m, rfl, rfl⟩)
    | _ => exact Or.inl rfl
  · split
    · rename_i hout
      cases σ with
      | M m => exact Or.inl rfl
      | _ =>
        refine Or.inr (Or.inl ⟨(fun m e => by cases e), fun e => ?_⟩)
        subst e
        simp [outsideMode, Gen.tgt?] at hout
    · cases σ with
      | M m => exact Or.inl rfl
      | _ => exact Or.inl rfl

theorem argOf_zeroP (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c γ : Tm) :
    argOf τ σ g pre R r c .zero γ = combine g pre c .zero (r.big γ) := by
  unfold argOf
  split
  · rfl
  · split
    · rfl
    · simp only [ite_self]

/-- `outFix` が `iapp` を作る条件 -/
theorem outFix_iapp_cond {τ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    {g' : Gen} {pre' : List Tm} {r' : SeqD} {P' c' : Tm} {s : SeqD}
    (h : outFix (.app τ g pre R r P c) = .iapp g' pre' r' P' c' s) :
    ∃ m e, r.dom = .big (.Xi m e) ∧ ltB (.Xi m e) τ = false ∧ outsideMode τ (.Xi m e) g pre R = true ∧
      ltB (.Psi (.Xi m e) (oadd (ofSummands pre) R)) (.Psi τ (oadd (ofSummands pre) R)) = true ∧
      g' = g ∧ pre' = pre ∧ r' = r ∧ P' = P ∧ c' = c := by
  simp only [outFix] at h
  cases hd : r.dom with
  | big σ =>
    rw [hd] at h
    cases σ with
    | Xi m e =>
      dsimp only at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        cases h
        exact ⟨m, e, rfl, hc.1.1, hc.1.2, hc.2, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    | _ => cases h
  | _ => rw [hd] at h; cases h

/-- `Ψ_σ(X) < Ψ_π(X)`（`π < σ`）なら `Ψ_π(X) < Ψ_σ(X)` でない -/
theorem not_lt_psi_of_ltB {π σ X : Tm} (hπ : WNF π) (hσ : WNF σ) (hπσ : Lt π σ)
    (h : ltB (.Psi σ X) (.Psi π X) = true) : ¬ Lt (.Psi π X) (.Psi σ X) := by
  have h' : Lt (.Psi σ X) (.Psi π X) := ltB_iff.mp h
  have hl1 : lev σ ≤ lev π := by have := lev_le_of_lt_gen h'; simpa [lev] using this
  have hl2 : lev π ≤ lev σ := lev_le_of_lt_gen hπσ
  have hl : lev π = lev σ := Nat.le_antisymm hl2 hl1
  have hb : baseOf π (.Psi σ X) = false := by
    rcases (lt_psi_psiY hl.symm).mp h' with ⟨e, -⟩ | ⟨-, -, hb⟩ | ⟨-, hn, -⟩
    · exact absurd e.symm (Lt.ne hπσ)
    · exact hb
    · exact absurd hπσ hn
  intro hlt
  rcases (lt_psi_psiY hl).mp hlt with ⟨e, -⟩ | ⟨-, hσπ, -⟩ | ⟨-, -, hb'⟩
  · exact Lt.ne hπσ e
  · exact Lt.asymmY hπ hσ hπσ hσπ
  · rw [hb] at hb'; cases hb'

/-! ### 極限の引数の崩壊の 0 番目 -/

/-- 極限の引数の崩壊の 0 番目は `Ψ_π(pre ⊕ (c ⊕ x))`（`x ≥ R[0]`） -/
theorem psi_lim_f0 {π X R : Tm} {pre : List Tm} (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R])
    (hns : ¬ isSucc X = true) :
    ∃ c x, fund (.Psi π X) .zero = .Psi π (apx pre c x) ∧ WNF c ∧ WNF x ∧ Le (fund R .zero) x ∧
      AdjShape π pre c := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have hR0 : R ≠ .zero := by intro e; rw [e] at hR; cases hR.2
  have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsX hR.2]; exact hns
  have hRi := inv_of R hR.1
  have hcs := cs_lim_eq (π := π) hX hsX hns
  cases hm : mkApp π (.psi π) pre R (info R).seq .zero .zero with
  | none => exact absurd (by rw [hcs, hm]; rfl) (cs_ne_none ht)
  | some s =>
    obtain ⟨c, rfl, hcF, hcS⟩ := mkApp_psi_wnf hπ hm
    rw [hm, Option.map_some, Option.getD_some] at hcs
    cases hd : dom R with
    | zero => exact absurd ((dom_eq_zero_iff hR.1).mp hd) hR0
    | one => exact absurd ((dom_eq_one_iff hR.1).mp hd) hRns
    | omega =>
      have hr : (info R).seq.dom = .omega := hd
      rw [outFix_app_eq (fun σ h => by rw [hr] at h; cases h)] at hcs
      have hdt : dom (.Psi π X) = .omega := by rw [dom_psi, hcs]; simp only [SeqD.dom, hr]
      have hxF : WNF (fundNat R 0) := (hRi.1 hd).props.nf 0
      refine ⟨c, fundNat R 0, ?_, hcF, hxF, by rw [fund_zero_omega hd]; exact Or.inl rfl, hcS⟩
      rw [fund_zero_omega hdt, fundNat_psi, hcs]
      simp only [SeqD.nat, hr, Gen.ap]
      exact congrArg (Tm.Psi π) (combine_psi_zero pre hcF hxF)
    | big σ =>
      have hr : (info R).seq.dom = .big σ := hd
      have hB := hRi.2 σ hd
      have hBP := hB.props
      have hR0F : WNF (fundBig R .zero) := hBP.nf _ WNF.zero hBP.pos
      have hfR : fund R .zero = fundBig R .zero := fund_zero_big hd
      by_cases hσπ : Lt σ π
      · have hlt : ltB σ π = true := ltB_iff.mpr hσπ
        rw [outFix_app_eq (fun σ' h => by rw [hr] at h; cases h; exact Or.inl hlt)] at hcs
        have hdt : dom (.Psi π X) = .big σ := by
          rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hlt, ↓reduceIte]
        refine ⟨c, fundBig R .zero, ?_, hcF, hR0F, by rw [hfR]; exact Or.inl rfl, hcS⟩
        rw [fund_zero_big hdt, fundBig_psi, hcs]
        simp only [SeqD.big, Gen.ap]
        exact congrArg (Tm.Psi π) (combine_psi_zero pre hcF hR0F)
      · have hlt : ltB σ π = false := by
          cases e : ltB σ π with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) hσπ
        rcases outFix_app π (.psi π) pre R (info R).seq .zero c with e | ⟨s', e⟩
        · -- 対角化（`app`）
          rw [e] at hcs
          have hdt : dom (.Psi π X) = .omega := by
            rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hlt, Bool.false_eq_true, ↓reduceIte]
          have fin : ∀ γ, γ = gam π σ (.psi π) pre R (info R).seq c .zero 0 → WNF γ →
              (γ = .zero ∨ Lt γ σ) → ∃ c x, fund (.Psi π X) .zero = .Psi π (apx pre c x) ∧ WNF c ∧
                WNF x ∧ Le (fund R .zero) x ∧ AdjShape π pre c := by
            intro γ hγ hγF0 hγF1
            have hxF : WNF (fundBig R γ) := by
              rcases hγF1 with h0 | h0
              · rw [h0]; exact hR0F
              · exact hBP.nf γ hγF0 h0
            refine ⟨c, fundBig R γ, ?_, hcF, hxF, ?_, hcS⟩
            · rw [fund_zero_omega hdt, fundNat_psi, hcs]
              simp only [SeqD.nat, hr, hlt, Bool.false_eq_true, ↓reduceIte, Gen.ap]
              rw [← hγ, argOf_zeroP]
              exact congrArg (Tm.Psi π) (combine_psi_zero pre hcF hxF)
            · rw [hfR]
              rcases hγF1 with h0 | h0
              · rw [h0]; exact Or.inl rfl
              · exact bigProps_mono_le hBP WNF.zero hγF0 (zero_le γ) h0
          rcases gam0_psi_cases π σ pre R (info R).seq c with h0 | ⟨hσM, hne⟩ | ⟨m, rfl, h0⟩
          · exact fin _ rfl (by rw [h0]; exact WNF.zero) (Or.inl h0)
          · -- 外に足す型：塔の性質から
            have hπσ : Lt π σ := by
              rcases triY hπ hBP.σF with h' | e' | h'
              · exact h'
              · exact absurd e'.symm hne
              · exact absurd h' hσπ
            by_cases hT : Lt (.Psi π X) (.Psi σ X)
            · obtain ⟨-, c', cσ, γ', T⟩ := inv_psi_diag_out_full ht hsX hns hd hB hπσ hσM hT
              have hxF := hBP.nf _ (T.γF 0) (T.γσ 0)
              obtain ⟨c'', hce, -, hcS'⟩ := mkApp_psi_wnf hπ T.hmk
              simp only [SeqD.app.injEq, true_and] at hce
              rw [← hce] at hcS'
              refine ⟨c', fundBig R (γ' 0), ?_, T.adj.cF, hxF, ?_, hcS'⟩
              · rw [fund_zero_omega hdt, T.f 0]
              · rw [hfR]; exact bigProps_mono_le hBP WNF.zero (T.γF 0) (zero_le _) (T.γσ 0)
            · exfalso
              obtain ⟨k', e'', p, c', heq, H⟩ := a2_mk ht hsX hns hd hB hπσ hσM hT (fun u _ hu => inv_of u hu)
              have h1 := H.hcs
              rw [hcs] at h1
              cases h1
          · have hπM : Lt π (.M m) := by
              rcases triY hπ hBP.σF with h' | e' | h'
              · exact h'
              · exact absurd e' (hP.tgt.notM m)
              · exact absurd h' hσπ
            obtain ⟨h1, h2, -⟩ := kTop_spec (pre := pre) (R := R) (r := (info R).seq) hBP.σF.M hπ hπM
            exact fin _ rfl (by rw [h0]; exact h1) (Or.inr (by rw [h0]; exact h2))
        · -- 族の閉包を添字にする場合（`A2`）
          obtain ⟨k, e', hrd, hlt', hout, hTt, -, -, -, -, -⟩ := outFix_iapp_cond e
          rw [hr] at hrd
          cases hrd
          have hσF := hBP.σF
          have hne : Tm.Xi k e' ≠ π := by
            intro h0
            simp [outsideMode, Gen.tgt?, h0] at hout
          have hπσ : Lt π (.Xi k e') := by
            rcases triY hπ hσF with h1 | h1 | h1
            · exact h1
            · exact absurd h1.symm hne
            · exact absurd h1 hσπ
          have hXe : X = oadd (ofSummands pre) R := eq_oadd_of_summands hX hsX
          have hT : ¬ Lt (.Psi π X) (.Psi (.Xi k e') X) := by
            rw [hXe]; exact not_lt_psi_of_ltB hπ hσF hπσ hTt
          obtain ⟨k', e'', p, c', heq, H⟩ := a2_mk ht hsX hns hd hB hπσ
            (fun m h0 => by cases h0) hT (fun u _ hu => inv_of u hu)
          cases heq
          rw [e] at hcs
          have hcs' := H.hcs
          rw [hcs] at hcs'
          simp only [SeqD.iapp.injEq, true_and] at hcs'
          obtain ⟨rfl, rfl⟩ := hcs'
          cases hs : (mahloVK k e' (info e').sums (.Xi k e') (some p)).dom with
          | zero => exact absurd hs (mahloVK_dom_ne _ _ _ _ _).1
          | one => exact absurd hs (mahloVK_dom_ne _ _ _ _ _).2
          | omega =>
            have F := famNat_a2 H hs
            have hdt : dom (.Psi π X) = .omega := by
              rw [dom_psi, hcs]; simp only [SeqD.dom, hs]
            have hxF : WNF (fundBig R ((mahloVK k e' (info e').sums (.Xi k e') (some p)).nat 0)) :=
              hBP.nf _ (F.F 0) (F.ltρ 0)
            refine ⟨c, _, ?_, hcF, hxF, ?_, hcS⟩
            · rw [fund_zero_omega hdt, fundNat_psi, hcs]
              simp only [SeqD.nat, Gen.ap]
              exact congrArg (Tm.Psi π) (combine_psi_zero pre hcF hxF)
            · rw [hfR]
              exact bigProps_mono_le hBP WNF.zero (F.F 0) (zero_le _) (F.ltρ 0)
          | big τ =>
            have F := famBig_a2 H hs
            have hdt : dom (.Psi π X) = .big τ := by
              rw [dom_psi, hcs]; simp only [SeqD.dom, hs]
            have hy0F := F.F .zero WNF.zero F.pos
            have hy0σ := F.ltρ .zero WNF.zero F.pos
            have hxF : WNF (fundBig R ((mahloVK k e' (info e').sums (.Xi k e') (some p)).big .zero)) :=
              hBP.nf _ hy0F hy0σ
            refine ⟨c, _, ?_, hcF, hxF, ?_, hcS⟩
            · rw [fund_zero_big hdt, fundBig_psi, hcs]
              simp only [SeqD.big, Gen.ap]
              exact congrArg (Tm.Psi π) (combine_psi_zero pre hcF hxF)
            · rw [hfR]
              exact bigProps_mono_le hBP WNF.zero hy0F (zero_le _) hy0σ

end MahloOCF.FS
