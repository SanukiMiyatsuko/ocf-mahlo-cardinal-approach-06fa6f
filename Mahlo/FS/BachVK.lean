import Mahlo.FS.BachSeed

/-! 族の閉包（`mahloVK`）の梯子。列の記述 `s` の梯子 `SeqLad s`（`ω` 型なら隣り合う項の区間の下界、
正則項型なら区間の下界の移送）を、閉包の各枝（塔・ずらし・種なしの近似・種つきの近似・`M_m` への対角化）
について示す。 -/

namespace MahloOCF.FS

open Tm

/-- 列の記述の梯子 -/
def SeqLad (s : SeqD) : Prop :=
  (s.dom = .omega → ∀ n, LBI (s.nat n) (s.nat (n + 1))) ∧
  (∀ σ, s.dom = .big σ → ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ →
    (ξ = .zero ∨ (isPrincipal ξ = true ∧ Lt (base σ) ξ)) → LBI ξ η → LBI (s.big ξ) (s.big η))

theorem binv_of_seqLad {t : Tm} (h : SeqLad (info t).seq) : BInv t := ⟨h.1, h.2⟩

/-- `Ω` について閉じた点の上の塔 -/
theorem seqLad_tower {G : Tm} (hG : WNF G) (hcl : G = .zero ∨ omegaFixed G = true) :
    SeqLad (.tower G) :=
  ⟨fun _ n => lbi_tower hG hcl (n + 1), fun σ hd => by simp [SeqD.dom] at hd⟩

/-- `pre ⊕ (0 # x) = pre ⊕ x` -/
theorem xa_zero (pre : List Tm) {x : Tm} (hx : WNF x) : xa pre .zero x = oadd (ofSummands pre) x := by
  show oadd _ (nsum .zero x) = _
  rw [zero_nsum x hx]

/-! ### 種なしの近似 -/

/-- 種なしの近似 `Ξ_m(pre ⊕ R[n])`（`R` は `ω` 型）の梯子：`q` の前線は 0 番目未満、列は単調 -/
theorem lad_app0_nat {m : Nat} {q R : Tm} {pre rest : List Tm} (G : XG m q .zero pre rest R)
    (hRd : dom R = .omega) (hRN : NatInv R) (hRb : BInv R)
    (hfront : ∀ f, f ∈ fr (.M m) q → Lt f (.Xi m (xa pre .zero (fundNat R 0))))
    (hmono : ∀ n, Le (.Xi m (xa pre .zero (fundNat R 0))) (.Xi m (xa pre .zero (fundNat R n)))) :
    ∀ n, LBI (.Xi m (xa pre .zero (fundNat R n))) (.Xi m (xa pre .zero (fundNat R (n + 1)))) := by
  intro n
  have hm := G.hm
  have hMF := G.hMF
  have hRP := hRN.props
  have hxF := hRP.nf
  have hcM : ∀ k, inC (fundNat R k) (xa pre .zero (fundNat R k)) (.M m) = true := fun k =>
    hRN.ub _ _ k (G.hAF (hxF k)) (G.xa0 (hxF k) (hRN.pos k)) (Cut.of_wnf hMF)
      (G.pre_inC (hxF k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) G.hqC R (by simp))
  have hy : ∀ k, WNF (.Xi m (xa pre .zero (fundNat R k))) := fun k =>
    G.nf (hxF k) (hRP.lt k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) (hcM k)
  have hS : Le q (succM m) := le_of_ne_gtY G.hqF (WNF.succM hm) G.ht.xi.2.2.1
  have hA'S : Lt (xa pre .zero (fundNat R (n + 1))) (succM m) :=
    lt_of_lt_of_leY (G.hAF (hxF _)) G.hqF (WNF.succM hm) (G.hAq (hxF _) (hRP.lt _)) hS
  have hy0F := hy 0
  have hyo : ∀ k, WNF (.Xi m (oadd (ofSummands pre) (fundNat R k))) := fun k => by
    rw [← xa_zero pre (hxF k)]; exact hy k
  rw [xa_zero pre (hxF (n + 1))] at hA'S
  rw [xa_zero pre (hxF n), xa_zero pre (hxF (n + 1))]
  refine lbi_app_step G.hNT (hxF n) (hxF (n + 1)) (Or.inr (hRP.mono n)) (hRP.lt (n + 1))
    (hRb.om hRd n) (hyo n) (hyo (n + 1)) hA'S (fun d hd hyd => ?_)
  rw [← xa_zero pre (hxF n)] at hyd
  have hqD : inC q q d = true := inC_self_of_fr G.hqC (fun f hf =>
    lt_of_lt_of_leY (fr_elem G.hqF hf).1 hy0F hd (hfront f hf)
      (Or.inr (lt_of_le_of_ltY hy0F (hy n) hd (hmono n) hyd)))
  have hpre := G.pre_inC (hxF (n + 1)) (hRN.gap (n + 1)) (fun h0 => absurd h0 (hRN.pos (n + 1))) hqD
  have hxC := hRN.ub _ _ (n + 1) (G.hAF (hxF _)) (G.xa0 (hxF _) (hRN.pos _)) (Cut.of_wnf hd)
    (hpre R (by simp))
  have := G.inC_A (hxF (n + 1)) (fun s hs => hpre s (List.mem_append_left _ hs)) (inC_zero _ _) hxC
  rwa [xa_zero pre (hxF (n + 1))] at this


/-- 種なしの近似 `Ξ_m(pre ⊕ R[ξ])`（`R` の共終数 `σ < M_m`）の区間の下界の移送 -/
theorem lad_app0_big {m : Nat} {q R σ : Tm} {pre rest : List Tm} (G : XG m q .zero pre rest R)
    (hRd : dom R = .big σ) (hB : BigInv R σ) (hRb : BInv R) (hσM : Lt σ (.M m))
    (hfront : ∀ f, f ∈ fr (.M m) q → Lt f (.Xi m (xa pre .zero (fundBig R .zero))))
    (hmono : ∀ ξ, WNF ξ → Lt ξ σ →
      Le (.Xi m (xa pre .zero (fundBig R .zero))) (.Xi m (xa pre .zero (fundBig R ξ)))) :
    ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ → (ξ = .zero ∨ (isPrincipal ξ = true ∧ Lt (base σ) ξ)) →
      LBI ξ η → LBI (.Xi m (xa pre .zero (fundBig R ξ))) (.Xi m (xa pre .zero (fundBig R η))) := by
  intro ξ η hξ hη hξη hησ hadm hL
  have hm := G.hm
  have hRP := hB.props
  have hσF := hRP.σF
  have h0σ := hRP.pos
  have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hσF hξη hησ
  rcases hξη with e | hlt
  · subst e; exact LBI.refl _ (G.big_wnf hB hσM hξ hξσ)
  have hxF : ∀ ζ, WNF ζ → Lt ζ σ → WNF (fundBig R ζ) := fun ζ hζ hζσ => hRP.nf ζ hζ hζσ
  have hy : ∀ ζ, WNF ζ → Lt ζ σ → WNF (.Xi m (xa pre .zero (fundBig R ζ))) :=
    fun ζ hζ hζσ => G.big_wnf hB hσM hζ hζσ
  have hy0F := hy .zero WNF.zero h0σ
  -- `σ < y_0`
  have hq0 : inC q q (.Xi m (xa pre .zero (fundBig R .zero))) = true := inC_self_of_fr G.hqC hfront
  have hpre0 := G.pre_inC (hxF .zero WNF.zero h0σ)
    (fun v hv hne hlt' => hB.gapP G.hRp .zero v WNF.zero h0σ hv hne hlt') (hB.pos .zero WNF.zero h0σ) hq0
  have hσC := hB.σC _ _ (Cut.of_wnf hy0F) (hpre0 R (by simp))
  have hσy0 : Lt σ (.Xi m (xa pre .zero (fundBig R .zero))) := coll_xi0 hy0F σ hσF hσC hσM
  have hη0 : η ≠ .zero := by intro e; subst e; exact not_lt_zero _ hlt
  have hx0 : fundBig R η ≠ .zero := by
    intro e
    rcases hB.ge η hη hησ with e' | h'
    · exact hη0 (e'.trans e)
    · rw [e] at h'; exact not_lt_zero _ h'
  have hS : Le q (succM m) := le_of_ne_gtY G.hqF (WNF.succM hm) G.ht.xi.2.2.1
  have hA'S : Lt (xa pre .zero (fundBig R η)) (succM m) :=
    lt_of_lt_of_leY (G.hAF (hxF η hη hησ)) G.hqF (WNF.succM hm)
      (G.hAq (hxF η hη hησ) (hRP.lt η hη hησ)) hS
  have hyo : ∀ ζ, WNF ζ → Lt ζ σ → WNF (.Xi m (oadd (ofSummands pre) (fundBig R ζ))) :=
    fun ζ hζ hζσ => by rw [← xa_zero pre (hxF ζ hζ hζσ)]; exact hy ζ hζ hζσ
  rw [xa_zero pre (hxF η hη hησ)] at hA'S
  rw [xa_zero pre (hxF ξ hξ hξσ), xa_zero pre (hxF η hη hησ)]
  refine lbi_app_step G.hNT (hxF ξ hξ hξσ) (hxF η hη hησ)
    (bigProps_mono_le hRP hξ hη (Or.inr hlt) hησ) (hRP.lt η hη hησ)
    (hRb.big σ hRd ξ η hξ hη (Or.inr hlt) hησ hadm hL) (hyo ξ hξ hξσ) (hyo η hη hησ) hA'S
    (fun d hd hyd => ?_)
  rw [← xa_zero pre (hxF ξ hξ hξσ)] at hyd
  have hy0d : Lt (.Xi m (xa pre .zero (fundBig R .zero))) d :=
    lt_of_le_of_ltY hy0F (hy ξ hξ hξσ) hd (hmono ξ hξ hξσ) hyd
  have hqD : inC q q d = true := inC_self_of_fr G.hqC (fun f hf =>
    lt_transY (fr_elem G.hqF hf).1 hy0F hd (hfront f hf) hy0d)
  have hpre := G.pre_inC (hxF η hη hησ)
    (fun v hv hne hlt' => hB.gapP G.hRp η v hη hησ hv hne hlt') (hB.pos η hη hησ) hqD
  have hσd : Lt σ d := lt_transY hσF hy0F hd hσy0 hy0d
  have hbF : WNF (base σ) := wnf_base hσF hB.σreg
  have hxC := hB.ub _ _ η (G.hAF (hxF η hη hησ)) (G.xa0 (hxF η hη hησ) hx0) (Cut.of_wnf hd) hη hησ
    (inC_of_lt_cut (Cut.of_wnf hd) _ hbF (lt_transY hbF hσF hd (base_lt hσF hB.σreg) hσd))
    (hpre R (by simp)) (inC_of_lt_cut (Cut.of_wnf hd) _ hη (lt_transY hη hσF hd hησ hσd))
  have := G.inC_A (hxF η hη hησ) (fun s hs => hpre s (List.mem_append_left _ hs)) (inC_zero _ _) hxC
  rwa [xa_zero pre (hxF η hη hησ)] at this

/-! ### `M_m` への対角化（包の形） -/

/-- `Ξ_m` の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`（`R` の共終数は `M_m`）の梯子：始点の段と、`q` の前線が `γ_1` 未満 -/
theorem lad_M {m : Nat} {q R : Tm} {pre rest : List Tm} (G : XG m q .zero pre rest R)
    (hRd : dom R = .big (.M m)) (hB : BigInv R (.M m)) (hRb : BInv R)
    {γ : Nat → Tm} (hγS : ∀ n, γ (n + 1) = .Xi m (xa pre .zero (fundBig R (γ n))))
    (hγF : ∀ n, WNF (γ n)) (hγM : ∀ n, Lt (γ n) (.M m)) (hγm : ∀ n, Lt (γ n) (γ (n + 1)))
    (hadm0 : γ 0 = .zero ∨ (isPrincipal (γ 0) = true ∧ Lt (base (.M m)) (γ 0)))
    (hstart : LBI (γ 0) (γ 1)) (hfront : ∀ f, f ∈ fr (.M m) q → Lt f (γ 1)) :
    ∀ n, LBI (γ n) (γ (n + 1)) := by
  have hm := G.hm
  have hRP := hB.props
  have hxF : ∀ n, WNF (fundBig R (γ n)) := fun n => hRP.nf _ (hγF n) (hγM n)
  have hS : Le q (succM m) := le_of_ne_gtY G.hqF (WNF.succM hm) G.ht.xi.2.2.1
  have hadm : ∀ n, γ n = .zero ∨ (isPrincipal (γ n) = true ∧ Lt (base (.M m)) (γ n)) := by
    intro n
    cases n with
    | zero => exact hadm0
    | succ n =>
      right
      have hyF := hγF (n + 1)
      rw [hγS n] at hyF ⊢
      exact ⟨rfl, floorLev_lt_xi hyF⟩
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
    have hLx : LBI (fundBig R (γ n)) (fundBig R (γ (n + 1))) :=
      hRb.big (.M m) hRd (γ n) (γ (n + 1)) (hγF n) (hγF _) (Or.inr (hγm n)) (hγM _) (hadm n) ih
    have hyo : ∀ k, WNF (.Xi m (oadd (ofSummands pre) (fundBig R (γ k)))) := fun k => by
      rw [← xa_zero pre (hxF k), ← hγS k]; exact hγF (k + 1)
    have hA'S : Lt (oadd (ofSummands pre) (fundBig R (γ (n + 1)))) (succM m) := by
      rw [← xa_zero pre (hxF _)]
      exact lt_of_lt_of_leY (G.hAF (hxF _)) G.hqF (WNF.succM hm)
        (G.hAq (hxF _) (hRP.lt _ (hγF _) (hγM _))) hS
    have h := lbi_app_step G.hNT (hxF n) (hxF (n + 1))
      (bigProps_mono_le hRP (hγF n) (hγF _) (Or.inr (hγm n)) (hγM _)) (hRP.lt _ (hγF _) (hγM _)) hLx
      (hyo n) (hyo (n + 1)) hA'S (fun d hd hyd => ?_)
    · rw [← xa_zero pre (hxF n), ← xa_zero pre (hxF (n + 1)), ← hγS n, ← hγS (n + 1)] at h
      exact h
    · rw [← xa_zero pre (hxF n), ← hγS n] at hyd
      have h1n : Le (γ 1) (γ (n + 1)) := seq_mono_le hγF hγm (by omega)
      have hqD : inC q q d = true := inC_self_of_fr G.hqC (fun f hf =>
        lt_of_lt_of_leY (fr_elem G.hqF hf).1 (hγF 1) hd (hfront f hf)
          (Or.inr (lt_of_le_of_ltY (hγF 1) (hγF _) hd h1n hyd)))
      have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R (γ (n + 1))) :=
        fun v hv hne hlt => hB.gapP G.hRp (γ (n + 1)) v (hγF _) (hγM _) hv hne hlt
      have hpre := G.pre_inC (hxF (n + 1)) hgap (hB.pos _ (hγF _) (hγM _)) hqD
      have hx0 : fundBig R (γ (n + 1)) ≠ .zero := by
        intro e
        have h0 : γ (n + 1) ≠ .zero := by
          have := hγF (n + 1); rw [hγS n]; intro e'; cases e'
        rcases hB.ge (γ (n + 1)) (hγF _) (hγM _) with e' | h'
        · exact h0 (e'.trans e)
        · rw [e] at h'; exact not_lt_zero _ h'
      have hxC := hB.ub _ _ (γ (n + 1)) (G.hAF (hxF _)) (G.xa0 (hxF _) hx0) (Cut.of_wnf hd) (hγF _)
        (hγM _) (inC_kTerm _ _ _) (hpre R (by simp)) (inC_of_lt_cut (Cut.of_wnf hd) _ (hγF _) hyd)
      have := G.inC_A (hxF (n + 1)) (fun s hs => hpre s (List.mem_append_left _ hs)) (inC_zero _ _) hxC
      rwa [xa_zero pre (hxF (n + 1))] at this


/-! ### 種つきの近似 -/

/-- 小さい元の併合は末尾に付く -/
theorem merge_small : ∀ (l : List Tm) (a : Tm), (∀ y, y ∈ l → leB y a = false) → merge [a] l = l ++ [a]
  | [], a, _ => by rw [merge.eq_2]; rfl
  | y :: ys, a, h => by
    rw [merge.eq_3, ite_eq_right (by rw [h y List.mem_cons_self]; decide),
      merge_small ys a (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    rfl

/-- 高い `pre ⊕ x` への種 `P'` の自然な和は末尾に付く：`pre ⊕ (P' # x) = (pre ⊕ x) ⊕ P'` -/
theorem xa_eq_high {m : Nat} {pre : List Tm} {R x P' : Tm} (hN : NFL (pre ++ [R])) (hx : WNF x)
    (hxR : Lt x R) (hPF : WNF P') (hPp : isPrincipal P' = true) (hPM : Lt P' (.M m)) (hMF : WNF (.M m))
    (hHhi : ∀ u, u ∈ summands (oadd (ofSummands pre) x) → ¬ Lt u (.M m)) :
    xa pre P' x = oadd (oadd (ofSummands pre) x) P' := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hHF := wnf_oadd hpreF hx
  have hsH : summands (oadd (ofSummands pre) x) = pre ++ summands x := summands_oadd_pre hN hx hxR
  have hNH : NFL (summands (oadd (ofSummands pre) x) ++ summands P') := nfl_high_low hHF hPF hMF hHhi hPM
  rw [hsH, summands_principal hPp] at hNH
  have hm1 : merge [P'] (summands x) = summands x ++ [P'] := by
    refine merge_small _ _ (fun y hy => ?_)
    have hyW := summands_WNF x hx y hy
    have hyM : ¬ Lt y (.M m) := hHhi y (by rw [hsH]; exact List.mem_append_right _ hy)
    cases e : leB y P' with
    | false => rfl
    | true =>
      exfalso
      have hle : Le y P' := le_of_ne_gtY hyW.1 hPF (leB_iff.mp e)
      exact hyM (lt_of_le_of_ltY hyW.1 hPF hMF hle hPM)
  have hns : nsum P' x = ofSummands (summands x ++ [P']) := by
    unfold nsum; rw [summands_principal hPp, hm1]
  have hN1 : NFL (pre ++ (summands x ++ [P'])) := by rw [← List.append_assoc]; exact hNH
  have hN2 : NFL (pre ++ summands x) := nfl_append_left hNH
  show oadd (ofSummands pre) (nsum P' x) = _
  rw [hns, ← ofSummands_append hN1, ← List.append_assoc, ofSummands_append hNH,
    ofSummands_append hN2, ofSummands_summands x hx]
  rfl

/-- 種つきの近似 `Ξ_m(pre ⊕ (P' # R[n]))`（`R` は `ω` 型で高い）の梯子 -/
theorem lad_seeded_nat {m : Nat} {q R P' B : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hP0 : P' ≠ .zero) (hP1 : Lt one P')
    (hRd : dom R = .omega) (hRN : NatInv R) (hRb : BInv R)
    (hRhi : ∀ n u, u ∈ summands (fundNat R n) → ¬ Lt u (.M m))
    (hprehi : ∀ u, u ∈ pre → ¬ Lt u (.M m))
    (hBF : WNF B) (hcl : XiClosed m P' B) (hTB : Le (ofSummands (pre ++ [R])) B)
    (hPL : ∀ n, LBI P' (.Xi m (xa pre P' (fundNat R n))))
    (hfrH : ∀ n f, f ∈ fr (.M m) (oadd (ofSummands pre) (fundNat R n)) → Lt f P') :
    ∀ n, LBI (.Xi m (xa pre P' (fundNat R n))) (.Xi m (xa pre P' (fundNat R (n + 1)))) := by
  intro n
  have hm := G.hm
  have hMF := G.hMF
  have hRP := hRN.props
  have hxF := hRP.nf
  have hPF := G.hPF
  have hPp : isPrincipal P' = true := by
    rcases G.hPp with h | h
    · exact absurd h hP0
    · exact h
  have hPM := G.hPM
  have hpreF := G.hpreF
  have hHhi : ∀ k u, u ∈ summands (oadd (ofSummands pre) (fundNat R k)) → ¬ Lt u (.M m) := by
    intro k u hu
    rw [summands_oadd_pre G.hNT (hxF k) (hRP.lt k)] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hprehi u hu
    · exact hRhi k u hu
  have he : ∀ k, xa pre P' (fundNat R k) = oadd (oadd (ofSummands pre) (fundNat R k)) P' := fun k =>
    xa_eq_high G.hNT (hxF k) (hRP.lt k) hPF hPp hPM hMF (hHhi k)
  have hcM : ∀ k, inC (fundNat R k) (xa pre P' (fundNat R k)) (.M m) = true := fun k =>
    hRN.ub _ _ k (G.hAF (hxF k)) (G.xa0 (hxF k) (hRN.pos k)) (Cut.of_wnf hMF)
      (G.pre_inC (hxF k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) G.hqC R (by simp))
  have hy : ∀ k, WNF (.Xi m (xa pre P' (fundNat R k))) := fun k =>
    G.nf (hxF k) (hRP.lt k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) (hcM k)
  have hS : Le q (succM m) := le_of_ne_gtY G.hqF (WNF.succM hm) G.ht.xi.2.2.1
  have hA'S : Lt (xa pre P' (fundNat R (n + 1))) (succM m) :=
    lt_of_lt_of_leY (G.hAF (hxF _)) G.hqF (WNF.succM hm) (G.hAq (hxF _) (hRP.lt _)) hS
  have hA'B : Lt (xa pre P' (fundNat R (n + 1))) B :=
    lt_of_lt_of_leY (G.hAF (hxF _)) G.hTF hBF (G.hAT (hxF _) (hRP.lt _)) hTB
  have hy0 := hy n
  have hy1 := hy (n + 1)
  have hP := hPL n
  rw [he n] at hy0 hP ⊢
  rw [he (n + 1)] at hy1 hA'S hA'B ⊢
  exact lbi_seeded (wnf_oadd hpreF (hxF n)) (wnf_oadd hpreF (hxF (n + 1))) hPF hPp hP1 hPM
    (hHhi n) (hHhi (n + 1)) (oadd_le_oadd hpreF (hxF n) (hxF _) (Or.inr (hRP.mono n)))
    (lbi_oadd_pre pre G.hNT (hxF n) (hxF _) (Or.inr (hRP.mono n)) (hRP.lt _) (hRb.om hRd n))
    hy0 hy1 hA'S hBF hcl hA'B hP (hfrH n) (hfrH (n + 1))

/-- 種つきの近似 `Ξ_m(pre ⊕ (P' # R[ξ]))`（`R` の共終数 `σ < M_m`、`R[ξ]` は高い）の区間の下界の移送 -/
theorem lad_seeded_big {m : Nat} {q R σ P' B : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hP0 : P' ≠ .zero) (hP1 : Lt one P')
    (hRd : dom R = .big σ) (hB : BigInv R σ) (hRb : BInv R) (hσM : Lt σ (.M m))
    (hRhi : ∀ ξ, WNF ξ → Lt ξ σ → ∀ u, u ∈ summands (fundBig R ξ) → ¬ Lt u (.M m))
    (hprehi : ∀ u, u ∈ pre → ¬ Lt u (.M m))
    (hBF : WNF B) (hcl : XiClosed m P' B) (hTB : Le (ofSummands (pre ++ [R])) B)
    (hPL : ∀ ξ, WNF ξ → Lt ξ σ → LBI P' (.Xi m (xa pre P' (fundBig R ξ))))
    (hfrH : ∀ ξ, WNF ξ → Lt ξ σ → ∀ f, f ∈ fr (.M m) (oadd (ofSummands pre) (fundBig R ξ)) → Lt f P') :
    ∀ ξ η, WNF ξ → WNF η → Le ξ η → Lt η σ → (ξ = .zero ∨ (isPrincipal ξ = true ∧ Lt (base σ) ξ)) →
      LBI ξ η → LBI (.Xi m (xa pre P' (fundBig R ξ))) (.Xi m (xa pre P' (fundBig R η))) := by
  intro ξ η hξ hη hξη hησ hadm hL
  have hm := G.hm
  have hMF := G.hMF
  have hRP := hB.props
  have hσF := hRP.σF
  have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hσF hξη hησ
  have hxF : ∀ ζ, WNF ζ → Lt ζ σ → WNF (fundBig R ζ) := fun ζ hζ hζσ => hRP.nf ζ hζ hζσ
  have hPF := G.hPF
  have hPp : isPrincipal P' = true := by
    rcases G.hPp with h | h
    · exact absurd h hP0
    · exact h
  have hPM := G.hPM
  have hpreF := G.hpreF
  have hHhi : ∀ ζ, WNF ζ → Lt ζ σ → ∀ u, u ∈ summands (oadd (ofSummands pre) (fundBig R ζ)) →
      ¬ Lt u (.M m) := by
    intro ζ hζ hζσ u hu
    rw [summands_oadd_pre G.hNT (hxF ζ hζ hζσ) (hRP.lt ζ hζ hζσ)] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hprehi u hu
    · exact hRhi ζ hζ hζσ u hu
  have he : ∀ ζ, WNF ζ → Lt ζ σ →
      xa pre P' (fundBig R ζ) = oadd (oadd (ofSummands pre) (fundBig R ζ)) P' :=
    fun ζ hζ hζσ => xa_eq_high G.hNT (hxF ζ hζ hζσ) (hRP.lt ζ hζ hζσ) hPF hPp hPM hMF (hHhi ζ hζ hζσ)
  have hy : ∀ ζ, WNF ζ → Lt ζ σ → WNF (.Xi m (xa pre P' (fundBig R ζ))) :=
    fun ζ hζ hζσ => G.big_wnf hB hσM hζ hζσ
  have hS : Le q (succM m) := le_of_ne_gtY G.hqF (WNF.succM hm) G.ht.xi.2.2.1
  have hA'S : Lt (xa pre P' (fundBig R η)) (succM m) :=
    lt_of_lt_of_leY (G.hAF (hxF η hη hησ)) G.hqF (WNF.succM hm)
      (G.hAq (hxF η hη hησ) (hRP.lt η hη hησ)) hS
  have hA'B : Lt (xa pre P' (fundBig R η)) B :=
    lt_of_lt_of_leY (G.hAF (hxF η hη hησ)) G.hTF hBF (G.hAT (hxF η hη hησ) (hRP.lt η hη hησ)) hTB
  have hy0 := hy ξ hξ hξσ
  have hy1 := hy η hη hησ
  have hP := hPL ξ hξ hξσ
  rw [he ξ hξ hξσ] at hy0 hP ⊢
  rw [he η hη hησ] at hy1 hA'S hA'B ⊢
  exact lbi_seeded (wnf_oadd hpreF (hxF ξ hξ hξσ)) (wnf_oadd hpreF (hxF η hη hησ)) hPF hPp hP1 hPM
    (hHhi ξ hξ hξσ) (hHhi η hη hησ)
    (oadd_le_oadd hpreF (hxF ξ hξ hξσ) (hxF η hη hησ) (bigProps_mono_le hRP hξ hη hξη hησ))
    (lbi_oadd_pre pre G.hNT (hxF ξ hξ hξσ) (hxF η hη hησ) (bigProps_mono_le hRP hξ hη hξη hησ)
      (hRP.lt η hη hησ) (hRb.big σ hRd ξ η hξ hη hξη hησ hadm hL))
    hy0 hy1 hA'S hBF hcl hA'B hP (hfrH ξ hξ hξσ) (hfrH η hη hησ)


/-! ### 始点の段（包の形） -/

/-- 逆向きの段（包の形）：`A' < F` なら `LBI (Ξ_m(F)) (Ξ_m(A'))` -/
theorem lbi_xi_inv_hull {m : Nat} {F A' : Tm} (hy : WNF (.Xi m F)) (hy' : WNF (.Xi m A'))
    (hA'F : Lt A' F) (hC : ∀ d, WNF d → Lt (.Xi m F) d → inC A' A' d = true) :
    LBI (.Xi m F) (.Xi m A') :=
  lbi_xi_step_hull hy hy' hC (fun _ hE hFE hEA' _ =>
    absurd (lt_of_lt_of_leY hy.xi.2.1 hE.xi.2.1 hy'.xi.2.1 hFE hEA')
      (Lt.asymmY hy'.xi.2.1 hy.xi.2.1 hA'F))

/-- 種 `p = Ψ_{Ξ_m(q)}(X)` から `Ξ_m(A')` まで（包の形）：`Ξ_m(A') < Ξ_m(q)` -/
theorem lbi_psi_seed_hull {m : Nat} {q X A' : Tm} (hp : WNF (.Psi (.Xi m q) X)) (hy' : WNF (.Xi m A'))
    (hA'q : Lt (.Xi m A') (.Xi m q))
    (hC : ∀ d, WNF d → Lt (.Psi (.Xi m q) X) d → inC A' A' d = true) :
    LBI (.Psi (.Xi m q) X) (.Xi m A') := by
  have hρ := hp.psi.piF
  have hOF : IsOF (Tm.Psi (.Xi m q) X) := Or.inr ⟨m, q, X, rfl⟩
  have hkp : Lt (kTerm (m - 1)) (.Psi (.Xi m q) X) :=
    kTerm_lt_of_lev hp rfl (fun k e => by cases e) rfl
  have hfar : ∀ E, WNF (.Xi m E) → Le (.Xi m q) (.Xi m E) →
      (Le (.Xi m E) (.Xi m A') ∨ ∃ C, WNF (.Psi (.Xi m E) C) ∧ Lt (.Psi (.Xi m q) X) (.Psi (.Xi m E) C) ∧
        Lt (.Psi (.Xi m E) C) (.Xi m A')) → False := by
    intro E hE hqE hrel
    have hnle : ¬ Le (.Xi m E) (.Xi m A') := fun hle =>
      Lt.irrefl _ (lt_of_le_of_ltY hρ hy' hρ (le_transY hρ hE hy' hqE hle) hA'q)
    rcases hrel with hle | ⟨C, hCF, h1, h2⟩
    · exact hnle hle
    · rcases (lt_psi_xiY (π := .Xi m E) (a := C) (b := A') (n := m) rfl).mp h2 with hc | hb
      · exact hnle (le_of_ne_gtY hE hy' hc)
      · have hk : Lt (kTerm (m - 1)) (.Psi (.Xi m E) C) := lt_transY (wnf_kTerm _) hp hCF hkp h1
        rw [(baseOf_xi_iff m _ _).mpr ⟨hk, hC _ hCF h1⟩] at hb
        cases hb
  refine lbi_xi_gen hp hOF rfl hy' (fun E hE hlt hrel => ?_)
  have hEF := hE.xi.2.1
  rcases (lt_psi_xiY (π := .Xi m q) (a := X) (b := E) (n := m) rfl).mp hlt with hc | hb
  · exact absurd hrel (fun h => hfar E hE (le_of_ne_gtY hρ hE hc) h)
  · have hEC : inC E E (.Psi (.Xi m q) X) = false := by
      cases e : inC E E (.Psi (.Xi m q) X) with
      | false => rfl
      | true => rw [(baseOf_xi_iff m _ _).mpr ⟨hkp, e⟩] at hb; cases hb
    obtain ⟨u, hu, hdu⟩ := front_witness hp (fun a _ h => h) E hEF hEC (xi_selfY hE)
    have hu' : u ∈ fr (.Xi m E) (.Xi m E) := by
      rw [fr]; simp only [Lt.irrefl, ↓reduceIte]; exact hu
    have huF := (fr_elem hE hu').1
    exact Or.inr (lt_of_le_of_ltY hp huF (wnf_f0 (wnf_base hE (Or.inr (Or.inr (Or.inr ⟨m, E, rfl⟩)))))
      hdu (front_lt_base_f0 hE hu'))

/-! ### 近似の引数の包 -/

/-- 近似の引数 `pre ⊕ (P' # R[ξ])` の包：`q ∈ C(q, d)`、種・添字・`σ` の底が `C(·, d)` に入れば -/
theorem inC_app_big {m : Nat} {q P' R σ ξ d : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hB : BigInv R σ) (hξ : WNF ξ) (hξσ : Lt ξ σ) (hx0 : fundBig R ξ ≠ .zero)
    (hd : WNF d) (hqD : inC q q d = true) (hPC : ∀ g, inC P' g d = true)
    (hbC : ∀ g, inC (base σ) g d = true) (hξC : ∀ g, inC ξ g d = true) :
    inC (xa pre P' (fundBig R ξ)) (xa pre P' (fundBig R ξ)) d = true := by
  have hRP := hB.props
  have hxF := hRP.nf ξ hξ hξσ
  have hpre := G.pre_inC hxF (fun v hv hne hlt => hB.gapP G.hRp ξ v hξ hξσ hv hne hlt)
    (hB.pos ξ hξ hξσ) hqD
  have hxC := hB.ub _ _ ξ (G.hAF hxF) (G.xa0 hxF hx0) (Cut.of_wnf hd) hξ hξσ (hbC _)
    (hpre R (by simp)) (hξC _)
  exact G.inC_A hxF (fun s hs => hpre s (List.mem_append_left _ hs)) (hPC _) hxC

/-- 近似の引数 `pre ⊕ (P' # R[n])` の包 -/
theorem inC_app_nat {m : Nat} {q P' R d : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRN : NatInv R) (n : Nat) (hd : WNF d) (hqD : inC q q d = true) (hPC : ∀ g, inC P' g d = true) :
    inC (xa pre P' (fundNat R n)) (xa pre P' (fundNat R n)) d = true := by
  have hRP := hRN.props
  have hxF := hRP.nf n
  have hpre := G.pre_inC hxF (hRN.gap n) (fun h0 => absurd h0 (hRN.pos n)) hqD
  have hxC := hRN.ub _ _ n (G.hAF hxF) (G.xa0 hxF (hRN.pos n)) (Cut.of_wnf hd) (hpre R (by simp))
  exact G.inC_A hxF (fun s hs => hpre s (List.mem_append_left _ hs)) (hPC _) hxC


/-! ### 種による前線の評価 -/

/-- 分割 `pre ⊕ R ⊕ rest` での種 `P'` の近似の前線の評価：`R` は `M_m` 以上で、`pre ⊕ R[·]` の前線は
`P'` 未満（共終数が `Ξ_m(q)` 未満の正則項 `σ` なら `σ ≤ P'`） -/
structure SplitFr (m : Nat) (q P' : Tm) (pre : List Tm) (R : Tm) : Prop where
  hi : ¬ Lt R (.M m)
  nat : dom R = .omega → ∀ n f, f ∈ fr (.M m) (oadd (ofSummands pre) (fundNat R n)) → Lt f P'
  big : ∀ σ, dom R = .big σ → Lt σ (.Xi m q) → Le σ P' ∧
    ∀ ξ, WNF ξ → Lt ξ σ → ∀ f, f ∈ fr (.M m) (oadd (ofSummands pre) (fundBig R ξ)) → Lt f P'

/-- 種 `P'` を閉じる包 `C(g, P')`：`q` の加数が入り、`C(q, Ξ_m(q))` にも入る `M_m` 未満の元は `P'` 未満 -/
structure SeedHull (m : Nat) (q P' g : Tm) : Prop where
  gF : WNF g
  g0 : g ≠ .zero
  sumC : ∀ s, s ∈ summands q → inC s g P' = true
  coll : ∀ z, WNF z → inC z g P' = true → inC z q (.Xi m q) = true → Lt z (.M m) → Lt z P'

/-- `pre ⊕ x`（`x` は `C(g, P')`・`C(q, Ξ_m(q))` に入る）の前線は `P'` 未満 -/
theorem fr_lt_of_hullS {m : Nat} {q P' R g x : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hsumC : ∀ s, s ∈ pre ++ [R] → inC s g P' = true)
    (hcoll : ∀ z, WNF z → inC z g P' = true → inC z q (.Xi m q) = true → Lt z (.M m) → Lt z P')
    (hx : WNF x) (hxg : inC x g P' = true) (hxq : inC x q (.Xi m q) = true) :
    ∀ f, f ∈ fr (.M m) (oadd (ofSummands pre) x) → Lt f P' := by
  have hMF := G.hMF
  have hρ := G.ht
  have hPF := G.hPF
  have hpreF := G.hpreF
  have hPM := G.hPM
  have hHF := wnf_oadd hpreF hx
  have hpreg : inC (ofSummands pre) g P' = true :=
    (inC_ofSummands pre).mpr (fun s hs => hsumC s (List.mem_append_left _ hs))
  have hpreq : inC (ofSummands pre) q (.Xi m q) = true :=
    (inC_ofSummands pre).mpr (fun s hs => G.pre_inCρ s (List.mem_append_left _ hs))
  have hHg : inC (oadd (ofSummands pre) x) g P' = true := inC_oadd hpreF hx hpreg hxg
  have hHq : inC (oadd (ofSummands pre) x) q (.Xi m q) = true := inC_oadd hpreF hx hpreq hxq
  intro f hf
  have hfF := (fr_elem hHF hf).1
  have hfM := (fr_elem hHF hf).2.1
  have hfg := inC_fr hPF hMF (Or.inr hPM) _ hHF hHg f hf
  have hfq := inC_fr hρ hMF (Or.inr (xi_lt_M q)) _ hHF hHq f hf
  exact hcoll f hfF hfg hfq hfM

/-- `R` の列の項は `C(q, Ξ_m(q))` に入る（`ω` 型） -/
theorem fundNat_inCρ {m : Nat} {q P' R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRN : NatInv R) (n : Nat) : inC (fundNat R n) q (.Xi m q) = true :=
  hRN.ub _ _ n G.hqF G.hq0 (Cut.of_wnf G.ht) (G.pre_inCρ R (by simp))

/-- `R` の列の項は `C(q, Ξ_m(q))` に入る（正則項型、`σ < Ξ_m(q)`） -/
theorem fundBig_inCρ {m : Nat} {q P' R σ ξ : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hB : BigInv R σ) (hσρ : Lt σ (.Xi m q)) (hξ : WNF ξ) (hξσ : Lt ξ σ) :
    inC (fundBig R ξ) q (.Xi m q) = true := by
  have hρ := G.ht
  have hσF := hB.props.σF
  have hbF : WNF (base σ) := wnf_base hσF hB.σreg
  exact hB.ub _ _ ξ G.hqF G.hq0 (Cut.of_wnf hρ) hξ hξσ
    (inC_of_lt_cut (Cut.of_wnf hρ) _ hbF (lt_transY hbF hσF hρ (base_lt hσF hB.σreg) hσρ))
    (G.pre_inCρ R (by simp)) (inC_of_lt_cut (Cut.of_wnf hρ) _ hξ (lt_transY hξ hσF hρ hξσ hσρ))

/-- 包 `C(g, P')`（`pre ++ [R]` の加数が入る）による分割の前線の評価 -/
theorem splitFr_of_hull {m : Nat} {q P' R g : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hgF : WNF g) (hg0 : g ≠ .zero) (hsumC : ∀ s, s ∈ pre ++ [R] → inC s g P' = true)
    (hcoll : ∀ z, WNF z → inC z g P' = true → inC z q (.Xi m q) = true → Lt z (.M m) → Lt z P')
    (hRi : Inv R) : SplitFr m q P' pre R := by
  have hρ := G.ht
  have hMF := G.hMF
  have hPF := G.hPF
  have hRg : inC R g P' = true := hsumC R (by simp)
  have hRq : inC R q (.Xi m q) = true := G.pre_inCρ R (by simp)
  refine ⟨fun h => Lt.asymmY hPF G.hRF G.hPR (hcoll R G.hRF hRg hRq h), fun hd n => ?_,
    fun σ hd hσρ => ?_⟩
  · have hRN := hRi.1 hd
    exact fr_lt_of_hullS G hsumC hcoll (hRN.props.nf n)
      (hRN.ub _ _ n hgF hg0 (Cut.of_wnf hPF) hRg) (fundNat_inCρ G hRN n)
  · have hB := hRi.2 σ hd
    have hσF := hB.props.σF
    have hσM : Lt σ (.M m) := lt_transY hσF hρ hMF hσρ (xi_lt_M q)
    have hσP : Lt σ P' :=
      hcoll σ hσF (hB.σC _ _ (Cut.of_wnf hPF) hRg) (hB.σC _ _ (Cut.of_wnf hρ) hRq) hσM
    have hbF : WNF (base σ) := wnf_base hσF hB.σreg
    have hbP : Lt (base σ) P' := lt_transY hbF hσF hPF (base_lt hσF hB.σreg) hσP
    refine ⟨Or.inr hσP, fun ξ hξ hξσ => ?_⟩
    have hξP : Lt ξ P' := lt_transY hξ hσF hPF hξσ hσP
    exact fr_lt_of_hullS G hsumC hcoll (hB.props.nf ξ hξ hξσ)
      (hB.ub _ _ ξ hgF hg0 (Cut.of_wnf hPF) hξ hξσ (inC_of_lt_cut (Cut.of_wnf hPF) _ hbF hbP) hRg
        (inC_of_lt_cut (Cut.of_wnf hPF) _ hξ hξP))
      (fundBig_inCρ G hB hσρ hξ hξσ)

/-- 加数が全て入る包による分割の前線の評価 -/
theorem SeedHull.splitFr {m : Nat} {q P' R g : Tm} {pre rest : List Tm} (S : SeedHull m q P' g)
    (G : XG m q P' pre rest R) (hRi : Inv R) : SplitFr m q P' pre R :=
  splitFr_of_hull G S.gF S.g0 (fun s hs => S.sumC s (by
    rcases List.mem_append.mp hs with hs | hs
    · exact G.hpreq hs
    · rw [List.mem_singleton.mp hs]; exact G.hRq)) S.coll hRi


/-! ### 種の性質のまとめ -/

/-- 種 `P'`（閉じていて、`q` の前線より大きく、近似までの区間の下界を持つ）-/
structure SeedPack (m : Nat) (q P' B : Tm) : Prop where
  F : WNF P'
  prin : isPrincipal P' = true
  one : Lt one P'
  ltρ : Lt P' (.Xi m q)
  of : omegaFixed P' = true
  bot : Lt (floorLev m) P'
  BF : WNF B
  closed : XiClosed m P' B
  lad : ∀ A, WNF (.Xi m A) → Lt A B → Lt (.Xi m A) (.Xi m q) →
    (∀ d, WNF d → Lt P' d → inC A A d = true) → LBI P' (.Xi m A)
  frq : ∀ f, f ∈ fr (.M m) q → Le f P'

theorem SeedPack.P0 {m : Nat} {q P' B : Tm} (S : SeedPack m q P' B) : P' ≠ .zero := by
  intro e; have := S.prin; rw [e] at this; cases this

/-- `q ∈ C(q, d)`（`d > P'`） -/
theorem SeedPack.qC {m : Nat} {q P' B d : Tm} (S : SeedPack m q P' B) (hqC : inC q q (.M m) = true)
    (hqF : WNF q) (hd : WNF d) (hPd : Lt P' d) : inC q q d = true :=
  inC_self_of_fr hqC (fun f hf => lt_of_le_of_ltY (fr_elem hqF hf).1 S.F hd (S.frq f hf) hPd)

/-- `Ξ_m(W)`（`q = W + 1`）の種の包 `C(W, Ξ_m(W))` -/
theorem seedHull_xi_pred {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true)
    (hW0 : predT q ≠ .zero) : SeedHull m q (.Xi m (predT q)) (predT q) := by
  have hqF := hρ.xi.2.1
  have hyF := xi_pred_wnf hρ hs
  have hWF := hyF.xi.2.1
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hsW : summands (predT q) = ys := summands_predT hqF hys
  have h1y : Lt one (.Xi m (predT q)) := one_lt_xi hyF
  refine ⟨hWF, hW0, fun s hs' => ?_, fun z hz hzg _ hzM => coll_xi0 hyF z hz hzg hzM⟩
  rw [hys] at hs'
  rcases List.mem_append.mp hs' with hs' | hs'
  · exact inC_of_mem_summands hWF (xi_selfY hyF) (by rw [hsW]; exact hs')
  · rw [List.mem_singleton.mp hs']
    exact inC_of_lt_node (Or.inr ⟨_, _, rfl⟩) h1y

/-- `Ξ_m(W)`（`q = W + 1`）の種 -/
theorem seedPack_xi_pred {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true) :
    SeedPack m q (.Xi m (predT q)) (predT q) := by
  have hm := hρ.xi.1
  have hMF := WNF.M' hm
  have hqF := hρ.xi.2.1
  have hyF := xi_pred_wnf hρ hs
  have hWF := hyF.xi.2.1
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hsW : summands (predT q) = ys := summands_predT hqF hys
  have h1y : Lt one (.Xi m (predT q)) := one_lt_xi hyF
  refine ⟨hyF, rfl, h1y, xi_pred_lt hρ hs, rfl, floorLev_lt_xi hyF, hWF, xiClosed_xi hyF,
    fun A hA hAW _ hC => lbi_xi_inv_hull hyF hA hAW (fun d hd hyd => hC d hd hyd), fun f hf => ?_⟩
  obtain ⟨v, hv, hfv⟩ := mem_fr_iff.mp hf
  rw [hys] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact Or.inr (fr_lt_xi hyF (mem_fr_iff.mpr ⟨v, by rw [hsW]; exact hv, hfv⟩))
  · rw [List.mem_singleton.mp hv] at hfv
    have h1M : Lt (Tm.Psi (.Om .zero) .zero) (.M m) :=
      lt_transY WNF.one hyF hMF h1y (xi_lt_M _)
    simp only [one, fr, h1M, ↓reduceIte, List.mem_singleton] at hfv
    rw [hfv]; exact Or.inr h1y

/-- `Ψ_{Ξ_m(q)}(X)`（`q < X`）の種の包 `C(X, Ψ_{Ξ_m(q)}(X))` -/
theorem seedHull_psi {m : Nat} {q X : Tm} (hp : WNF (.Psi (.Xi m q) X)) (hqX : Lt q X) :
    SeedHull m q (.Psi (.Xi m q) X) X := by
  have hρ := hp.psi.piF
  have hqF := hρ.xi.2.1
  have hXF := hp.psi.aF
  obtain ⟨-, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hp)
  have hqCX : inC q X (.Psi (.Xi m q) X) = true :=
    inC_mono q q _ X _ hqC (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq hqX)
  have hX0 : X ≠ .zero := by intro e; rw [e] at hqX; exact not_lt_zero _ hqX
  exact ⟨hXF, hX0, fun s hs => inC_of_mem_summands hqF hqCX hs,
    fun z hz hzg hzq hzM => coll_psiY hp hz hzg (coll_xi0 hρ z hz hzq hzM)⟩

/-- `Ψ_{Ξ_m(q)}(X)`（`q < X`）の種 -/
theorem seedPack_psi {m : Nat} {q X : Tm} (hp : WNF (.Psi (.Xi m q) X)) (hqX : Lt q X) :
    SeedPack m q (.Psi (.Xi m q) X) q := by
  have hρ := hp.psi.piF
  have hm := hρ.xi.1
  have hMF := WNF.M' hm
  have hqF := hρ.xi.2.1
  have hXF := hp.psi.aF
  have hpρ : Lt (.Psi (.Xi m q) X) (.Xi m q) := lt_psi_targetY hp
  obtain ⟨hk, hqC⟩ := (baseOf_xi_iff m q _).mp (base_selfY hp)
  have hqCX : inC q X (.Psi (.Xi m q) X) = true :=
    inC_mono q q _ X _ hqC (fun _ _ h => h)
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hXF hvq hqX)
  have hX0 : X ≠ .zero := by intro e; rw [e] at hqX; exact not_lt_zero _ hqX
  have h1p : Lt one (.Psi (.Xi m q) X) := coll_psiY hp WNF.one (inC_one hX0) (one_lt_xi hρ)
  refine ⟨hp, rfl, h1p, hpρ, rfl, hk, hqF, xiClosed_psi hp hqX,
    fun A hA _ hAρ hC => lbi_psi_seed_hull hp hA hAρ hC, fun f hf => ?_⟩
  have hfF := (fr_elem hqF hf).1
  have hfC := inC_fr hp hMF (Or.inr (lt_transY hp hρ hMF hpρ (xi_lt_M q))) q hqF hqCX f hf
  exact Or.inr (coll_psiY hp hfF hfC (fr_lt_xi hρ hf))


/-! ### 近似の梯子（種つき） -/

/-- `M_m < R < M_m⁺` の `R`（`Ψ_{M_m⁺}(Y)`）の列の項は高く、`0` でない -/
theorem high_fs_of_between {m : Nat} {R : Tm} (hm : 1 ≤ m) (hR : WNF R) (hRp : isPrincipal R = true)
    (h1 : Lt (.M m) R) (h2 : Lt R (succM m)) :
    (dom R = .omega → ∀ n u, u ∈ summands (fundNat R n) → ¬ Lt u (.M m)) ∧
    (∀ σ, dom R = .big σ → ∀ ξ, WNF ξ → Lt ξ σ →
      (∀ u, u ∈ summands (fundBig R ξ) → ¬ Lt u (.M m)) ∧ fundBig R ξ ≠ .zero) := by
  obtain ⟨Y, rfl⟩ := prin_between_M hm hR hRp h1 h2
  refine ⟨(psiS_fs_high hm hR).1, fun σ hd ξ hξ hξσ => ⟨(psiS_fs_high hm hR).2 σ hd ξ hξ hξσ, ?_⟩⟩
  intro e
  have hB := (inv_of _ hR).2 σ hd
  have := hB.pos ξ hξ hξσ e (succM m) (subs_psi_p (self_mem_subs _))
  cases this

/-- 種つきの近似 `app`（種 `P'`、`R` は `M_m` 以上で `M_m⁺` でない）の梯子 -/
theorem seqLad_app_seeded {m : Nat} {q P' B R : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (SP : SeedPack m q P' B) (SF : SplitFr m q P' pre R) (hTB : Le (ofSummands (pre ++ [R])) B)
    (hRi : Inv R) (hRb : BInv R) (hRS : R ≠ succM m)
    (hSnat : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).dom = .omega → ∀ n,
      WNF ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat n) ∧
      Lt ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat n)
        ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat (n + 1))) :
    SeqLad (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero) := by
  have hRM := SF.hi
  have hm := G.hm
  have hMF := G.hMF
  have hρ := G.ht
  have hqF := G.hqF
  have hRF := G.hRF
  have hPF := SP.F
  have hP0 := SP.P0
  have hP1 := SP.one
  have hPp := SP.prin
  have hPM := G.hPM
  have hPρ := SP.ltρ
  have hSF := WNF.succM hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hR1 : ¬ isSucc R = true := not_succ_of_gt hPF hPp G.hRp G.hPR
  have hMR : Le (.M m) R := le_of_not_ltY hRF hMF hRM
  have hprehi : ∀ u, u ∈ pre → ¬ Lt u (.M m) := by
    intro u hu h
    have huW := G.hNT.1 u (List.mem_append_left _ hu)
    have hRu : Le R u := le_of_ne_gtY hRF huW.1 (nfl_append_ge G.hNT u hu R (by simp))
    exact hRM (lt_of_le_of_ltY hRF huW.1 hMF hRu h)
  have hqS : Le q (succM m) := le_of_ne_gtY hqF hSF hρ.xi.2.2.1
  have hRlt : Lt R (succM m) := by
    rcases le_transY hRF hqF hSF (le_of_mem_summands hqF G.hRq) hqS with e | h
    · exact absurd e hRS
    · exact h
  have hPd : ∀ d, WNF d → Lt P' d → ∀ g', inC P' g' d = true :=
    fun d hd h g' => inC_of_lt_cut (Cut.of_wnf hd) _ hPF h
  have hPq : inC P' q (.Xi m q) = true := inC_of_lt_cut (Cut.of_wnf hρ) _ hPF hPρ
  cases hdR : dom R with
  | zero => exact absurd ((dom_eq_zero_iff hRF).mp hdR) G.hR0
  | one => exact absurd ((dom_eq_one_iff hRF).mp hdR) hR1
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    have hRP := hRN.props
    have hxF := hRP.nf
    have hMR' : Lt (.M m) R := by
      rcases hMR with e | h
      · rw [← e, dom_M] at hdR; cases hdR
      · exact h
    have hRhi := (high_fs_of_between hm hRF G.hRp hMR' hRlt).1 hdR
    refine ⟨fun _ n => ?_, fun σ hd => by rw [app_xi_dom_nat hr] at hd; cases hd⟩
    rw [app_xi_nat hr hPF (hxF n), app_xi_nat hr hPF (hxF (n + 1))]
    refine lad_seeded_nat G hP0 hP1 hdR hRN hRb hRhi hprehi SP.BF SP.closed hTB (fun k => ?_)
      (fun k => SF.nat hdR k) n
    have hcM : inC (fundNat R k) (xa pre P' (fundNat R k)) (.M m) = true :=
      hRN.ub _ _ k (G.hAF (hxF k)) (G.xa0 (hxF k) (hRN.pos k)) (Cut.of_wnf hMF)
        (G.pre_inC (hxF k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) G.hqC R (by simp))
    have hy := G.nf (hxF k) (hRP.lt k) (hRN.gap k) (fun h0 => absurd h0 (hRN.pos k)) hcM
    exact SP.lad _ hy (lt_of_lt_of_leY (G.hAF (hxF k)) G.hTF SP.BF (G.hAT (hxF k) (hRP.lt k)) hTB)
      (G.ltρ (hxF k) (hRP.lt k) (fundNat_inCρ G hRN k) hPq)
      (fun d hd hPd' => inC_app_nat G hRN k hd (SP.qC G.hqC hqF hd hPd') (hPd d hd hPd'))
  | big σ =>
    have hr : (info R).seq.dom = .big σ := hdR
    have hB := hRi.2 σ hdR
    have hRP := hB.props
    have hσF := hRP.σF
    by_cases hσρ : Lt σ (.Xi m q)
    · have hσM : Lt σ (.M m) := lt_transY hσF hρ hMF hσρ hρM
      have hMR' : Lt (.M m) R := by
        rcases hMR with e | h
        · rw [← e, dom_M] at hdR; cases hdR
          exact absurd hσρ (Lt.asymmY hρ hMF hρM)
        · exact h
      have hRhi := (high_fs_of_between hm hRF G.hRp hMR' hRlt).2 σ hdR
      have hdom := app_xi_big_dom (τ := .Xi m q) (R := R) (P' := P') (m := m) (pre := pre) hr hσρ
      refine ⟨(fun hd => by rw [hdom] at hd; cases hd), fun σ' hd => ?_⟩
      rw [hdom] at hd; cases hd
      intro ξ η hξ hη hξη hησ hadm hL
      have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hσF hξη hησ
      rw [app_xi_big hPF (hRP.nf ξ hξ hξσ), app_xi_big hPF (hRP.nf η hη hησ)]
      obtain ⟨hσP, hfrB⟩ := SF.big σ hdR hσρ
      refine lad_seeded_big G hP0 hP1 hdR hB hRb hσM (fun ζ hζ hζσ => (hRhi ζ hζ hζσ).1) hprehi SP.BF
        SP.closed hTB (fun ζ hζ hζσ => ?_) hfrB ξ η hξ hη hξη hησ hadm hL
      have hy := G.big_wnf hB hσM hζ hζσ
      have hbF : WNF (base σ) := wnf_base hσF hB.σreg
      have hσd : ∀ d, WNF d → Lt P' d → Lt σ d := fun d hd hPd' => lt_of_le_of_ltY hσF hPF hd hσP hPd'
      exact SP.lad _ hy (lt_of_lt_of_leY (G.hAF (hRP.nf ζ hζ hζσ)) G.hTF SP.BF
          (G.hAT (hRP.nf ζ hζ hζσ) (hRP.lt ζ hζ hζσ)) hTB)
        (G.ltρ (hRP.nf ζ hζ hζσ) (hRP.lt ζ hζ hζσ) (fundBig_inCρ G hB hσρ hζ hζσ) hPq)
        (fun d hd hPd' => inC_app_big G hB hζ hζσ (hRhi ζ hζ hζσ).2 hd (SP.qC G.hqC hqF hd hPd')
          (hPd d hd hPd')
          (fun g' => inC_of_lt_cut (Cut.of_wnf hd) _ hbF
            (lt_transY hbF hσF hd (base_lt hσF hB.σreg) (hσd d hd hPd')))
          (fun g' => inC_of_lt_cut (Cut.of_wnf hd) _ hζ (lt_transY hζ hσF hd hζσ (hσd d hd hPd'))))
    · rcases cof_split hρ G.hRq hB hσρ with e | ⟨-, eR, -⟩
      · subst e
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        have G0 : XG m q .zero pre rest R :=
          ⟨hρ, G.hsum, WNF.zero, zero_lt G.hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
        have hdom := app_xi_M_dom (τ := .Xi m q) (R := R) (P' := P') (m := m) (pre := pre) hr hτ
        refine ⟨fun hd n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
        obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam (.Xi m q) (.M m) (.xi m) pre R (info R).seq .zero P' :=
          ⟨_, rfl⟩
        have hγ0 : γ 0 = P' := by rw [hγdef]; exact gam_xi_M_zero
        have hnat : ∀ k, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).nat k = γ (k + 1) := by
          intro k; rw [app_xi_M_nat hr hτ, hγdef]
        have hSn := hSnat hd
        have hγF : ∀ k, WNF (γ k) := by
          intro k
          cases k with
          | zero => rw [hγ0]; exact hPF
          | succ k => rw [← hnat k]; exact (hSn k).1
        have hγS0 : ∀ k, γ (k + 1) = .Xi m (combine (.xi m) pre .zero .zero ((info R).seq.big (γ k))) := by
          intro k; rw [hγdef, gam_xi_M_succ]
        have hγM : ∀ k, Lt (γ k) (.M m) := by
          intro k
          cases k with
          | zero => rw [hγ0]; exact hPM
          | succ k => rw [hγS0 k]; exact xi_lt_M _
        have hγS : ∀ k, γ (k + 1) = .Xi m (xa pre .zero (fundBig R (γ k))) := by
          intro k
          rw [hγS0 k]
          exact congrArg (Tm.Xi m) (combine_xi m pre WNF.zero (hRP.nf _ (hγF k) (hγM k)))
        have hxP := hRP.nf P' hPF hPM
        have hγ1 : γ 1 = .Xi m (xa pre .zero (fundBig R P')) := by rw [hγS 0, hγ0]
        have hγ1F : WNF (.Xi m (xa pre .zero (fundBig R P'))) := by rw [← hγ1]; exact hγF 1
        have hPγ1 : Lt P' (γ 1) := by
          rw [hγ1]
          have h1 := (G0.parts hxP (hRP.lt P' hPF hPM) (xi_selfY hγ1F)).2.2
          exact coll_xi0 hγ1F P' hPF (hB.lo _ _ P' (Cut.of_wnf hγ1F) hPF hPM h1) hPM
        have hγm : ∀ k, Lt (γ k) (γ (k + 1)) := by
          intro k
          cases k with
          | zero => show Lt (γ 0) (γ 1); rw [hγ0]; exact hPγ1
          | succ k => rw [← hnat k, ← hnat (k + 1)]; exact (hSn k).2
        have hx0 : fundBig R P' ≠ .zero := by
          intro e
          rcases hB.ge P' hPF hPM with e' | h'
          · exact hP0 (e'.trans e)
          · rw [e] at h'; exact not_lt_zero _ h'
        have hstart : LBI (γ 0) (γ 1) := by
          rw [hγ0, hγ1]
          exact SP.lad _ hγ1F (lt_of_lt_of_leY (G0.hAF hxP) G0.hTF SP.BF
              (G0.hAT hxP (hRP.lt P' hPF hPM)) hTB)
            (G0.ltρ hxP (hRP.lt P' hPF hPM) (hB.ub _ _ P' hqF G.hq0 (Cut.of_wnf hρ) hPF hPM
              (inC_kTerm _ _ _) (G.pre_inCρ R (by simp)) hPq) (inC_zero _ _))
            (fun d hd hPd' => inC_app_big G0 hB hPF hPM hx0 hd (SP.qC G.hqC hqF hd hPd')
              (fun _ => inC_zero _ _) (fun _ => inC_kTerm _ _ _) (hPd d hd hPd'))
        rw [hnat n, hnat (n + 1)]
        exact lad_M G0 hdR hB hRb hγS hγF hγM hγm (Or.inr ⟨by rw [hγ0]; exact hPp, by rw [hγ0]; exact SP.bot⟩)
          hstart (fun f hf => lt_of_le_of_ltY (fr_elem hqF hf).1 hPF (hγF 1) (SP.frq f hf) hPγ1) (n + 1)
      · exact absurd eR hRS


/-! ### 近似の梯子（種なし） -/

/-- 種なしの近似 `app`（`R` は `M_m⁺` でない）の梯子：`q` の前線は 0 番目未満、列は単調 -/
theorem seqLad_app_seedless {m : Nat} {q R : Tm} {pre rest : List Tm} (G : XG m q .zero pre rest R)
    (hRi : Inv R) (hRb : BInv R) (hR1 : ¬ isSucc R = true) (hRS : R ≠ succM m)
    (hfront : ∀ f, f ∈ fr (.M m) q →
      Lt f (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).first)
    (hSnat : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).dom = .omega → ∀ n,
      WNF ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).nat n) ∧
      Lt ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).nat n)
        ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).nat (n + 1)))
    (hSbig : ∀ σ, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).dom = .big σ →
      ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
      Lt ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).big ξ)
        ((SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).big η)) :
    SeqLad (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero) := by
  have hMF := G.hMF
  have hρ := G.ht
  have hRF := G.hRF
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  cases hdR : dom R with
  | zero => exact absurd ((dom_eq_zero_iff hRF).mp hdR) G.hR0
  | one => exact absurd ((dom_eq_one_iff hRF).mp hdR) hR1
  | omega =>
    have hr : (info R).seq.dom = .omega := hdR
    have hRN := hRi.1 hdR
    have hRP := hRN.props
    have hxF := hRP.nf
    have hdom := app_xi_dom_nat (τ := .Xi m q) (R := R) (P' := .zero) (m := m) (pre := pre) hr
    have hnat : ∀ n, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).nat n =
        .Xi m (xa pre .zero (fundNat R n)) := fun n => app_xi_nat hr WNF.zero (hxF n)
    have hfirst : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).first =
        .Xi m (xa pre .zero (fundNat R 0)) := by
      unfold SeqD.first; rw [hdom]; exact hnat 0
    have hSn := hSnat hdom
    refine ⟨fun _ n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
    rw [hnat n, hnat (n + 1)]
    refine lad_app0_nat G hdR hRN hRb (fun f hf => by rw [← hfirst]; exact hfront f hf) (fun k => ?_) n
    rw [← hnat 0, ← hnat k]
    exact seq_mono_le (fun j => (hSn j).1) (fun j => (hSn j).2) (Nat.zero_le k)
  | big σ =>
    have hr : (info R).seq.dom = .big σ := hdR
    have hB := hRi.2 σ hdR
    have hRP := hB.props
    have hσF := hRP.σF
    by_cases hσρ : Lt σ (.Xi m q)
    · have hσM : Lt σ (.M m) := lt_transY hσF hρ hMF hσρ hρM
      have hdom := app_xi_big_dom (τ := .Xi m q) (R := R) (P' := .zero) (m := m) (pre := pre) hr hσρ
      have hbig : ∀ ξ, WNF ξ → Lt ξ σ → (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).big ξ =
          .Xi m (xa pre .zero (fundBig R ξ)) := fun ξ hξ hξσ => app_xi_big WNF.zero (hRP.nf ξ hξ hξσ)
      have hfirst : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).first =
          .Xi m (xa pre .zero (fundBig R .zero)) := by
        unfold SeqD.first; rw [hdom]; exact hbig .zero WNF.zero hRP.pos
      refine ⟨(fun hd => by rw [hdom] at hd; cases hd), fun σ' hd => ?_⟩
      rw [hdom] at hd; cases hd
      intro ξ η hξ hη hξη hησ hadm hL
      have hξσ : Lt ξ σ := lt_of_le_of_ltY hξ hη hσF hξη hησ
      rw [hbig ξ hξ hξσ, hbig η hη hησ]
      refine lad_app0_big G hdR hB hRb hσM (fun f hf => by rw [← hfirst]; exact hfront f hf)
        (fun ζ hζ hζσ => ?_) ξ η hξ hη hξη hησ hadm hL
      by_cases hζ0 : ζ = .zero
      · subst hζ0; exact Or.inl rfl
      · rw [← hbig .zero WNF.zero hRP.pos, ← hbig ζ hζ hζσ]
        exact Or.inr (hSbig σ hdom .zero ζ WNF.zero hζ (zero_lt hζ0) hζσ)
    · rcases cof_split hρ G.hRq hB hσρ with e | ⟨-, eR, -⟩
      · subst e
        have hτ : ltB (.M m) (.Xi m q) = false := by
          cases e : ltB (.M m) (.Xi m q) with
          | false => rfl
          | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hρ hMF hρM)
        have hdom := app_xi_M_dom (τ := .Xi m q) (R := R) (P' := .zero) (m := m) (pre := pre) hr hτ
        refine ⟨fun hd n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
        obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm,
            γ = gam (.Xi m q) (.M m) (.xi m) pre R (info R).seq .zero .zero := ⟨_, rfl⟩
        have hγ0 : γ 0 = .zero := by rw [hγdef]; exact gam_xi_M_zero
        have hnat : ∀ k, (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).nat k = γ (k + 1) := by
          intro k; rw [app_xi_M_nat hr hτ, hγdef]
        have hSn := hSnat hd
        have hγF : ∀ k, WNF (γ k) := by
          intro k
          cases k with
          | zero => rw [hγ0]; exact WNF.zero
          | succ k => rw [← hnat k]; exact (hSn k).1
        have hγS0 : ∀ k, γ (k + 1) = .Xi m (combine (.xi m) pre .zero .zero ((info R).seq.big (γ k))) := by
          intro k; rw [hγdef, gam_xi_M_succ]
        have hγM : ∀ k, Lt (γ k) (.M m) := by
          intro k
          cases k with
          | zero => rw [hγ0]; exact zero_lt (by intro e; cases e)
          | succ k => rw [hγS0 k]; exact xi_lt_M _
        have hγS : ∀ k, γ (k + 1) = .Xi m (xa pre .zero (fundBig R (γ k))) := by
          intro k
          rw [hγS0 k]
          exact congrArg (Tm.Xi m) (combine_xi m pre WNF.zero (hRP.nf _ (hγF k) (hγM k)))
        have hγm : ∀ k, Lt (γ k) (γ (k + 1)) := by
          intro k
          cases k with
          | zero =>
            show Lt (γ 0) (γ 1); rw [hγ0]
            exact zero_lt (by rw [hγS 0]; intro e; cases e)
          | succ k => rw [← hnat k, ← hnat (k + 1)]; exact (hSn k).2
        have hfirst : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq .zero .zero).first = γ 1 := by
          unfold SeqD.first; rw [hdom]; exact hnat 0
        rw [hnat n, hnat (n + 1)]
        exact lad_M G hdR hB hRb hγS hγF hγM hγm (Or.inl hγ0) (by rw [hγ0]; exact lbi_zero _)
          (fun f hf => by rw [← hfirst]; exact hfront f hf) (n + 1)
      · exact absurd eR hRS


/-! ### 仮想的な塔（`q = M_m⁺`） -/

theorem outsideMode_SS (m : Nat) :
    outsideMode (succM m) (succM m) (.psi (succM m)) [] (succM m) = false := by
  simp [outsideMode, succM, Gen.tgt?]

theorem canonK_SS (m : Nat) : canonK (succM m) (.psi (succM m)) [] (succM m) = false := by
  simp [canonK, succM]

/-- `Ψ_{M_m⁺}(M_m⁺)` の列の記述 -/
theorem cs_SS (m : Nat) :
    cs (succM m) (succM m) = .app (succM m) (.psi (succM m)) [] (succM m) (info (succM m)).seq .zero .zero := by
  unfold cs cseq
  rw [ite_eq_right (by intro e; cases e)]
  have hsums : (info (succM m)).sums = [(succM m, (info (succM m)).seq)] := by
    show (info (.Om (.plus (.M m) one))).sums = _
    rfl
  have hl : (lastS (info (succM m)).sums).dom = .big (succM m) := by
    rw [hsums, info_seq_succM]; rfl
  rw [hl]
  dsimp only
  unfold limitSeq
  rw [hsums]
  simp only [preT, lastT, lastS, List.dropLast_singleton, List.map_nil, List.getLast?_singleton,
    Option.map_some, Option.getD_some]
  rw [info_seq_succM]
  simp [mkApp, Gen.tgt?, tailRaw, argR?, outFix, SeqD.dom, succM]

/-- `Ψ_{M_m⁺}(M_m⁺)` の列は仮想的な塔 -/
theorem gam_SS {m : Nat} (hm : 1 ≤ m) (k : Nat) :
    gam (succM m) (succM m) (.psi (succM m)) [] (succM m) (info (succM m)).seq .zero .zero k = virtG m k := by
  induction k with
  | zero =>
    simp only [gam, canonK_SS, outsideMode_SS, Bool.false_eq_true, ↓reduceIte]
    rfl
  | succ k ih =>
    simp only [gam, canonK_SS, outsideMode_SS, Bool.false_eq_true, ↓reduceIte, argOf, seedOut, Gen.ap]
    rw [ih, info_seq_succM]
    show Tm.Psi (succM m) (combine (.psi (succM m)) [] .zero (if true && virtG m k == .zero then .zero else .zero)
      (oadd (.Psi (succM m) .zero) (virtG m k))) = virtG m (k + 1)
    have e : (if true && virtG m k == .zero then (.zero : Tm) else .zero) = .zero := by split <;> rfl
    rw [e]
    show Tm.Psi (succM m) (oadd (ofSummands []) (nsum (oadd .zero (oadd (.Psi (succM m) .zero) (virtG m k))) .zero)) = _
    rw [zero_oadd (virtE_F hm k), nsum_zero _ (virtE_F hm k),
      show ofSummands ([] : List Tm) = .zero from rfl, zero_oadd (virtE_F hm k)]
    rfl

theorem fundNat_SS {m : Nat} (hm : 1 ≤ m) (n : Nat) :
    fundNat (.Psi (succM m) (succM m)) n = virtG m (n + 1) := by
  rw [fundNat_psi, cs_SS]
  have hr : (info (succM m)).seq.dom = .big (succM m) := by rw [info_seq_succM]; rfl
  have hl : ltB (succM m) (succM m) = false := by
    cases e : ltB (succM m) (succM m) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.irrefl _)
  simp only [SeqD.nat, hr, hl, Bool.false_eq_true, ↓reduceIte]
  rw [← gam_SS hm (n + 1)]
  simp only [gam, canonK_SS, outsideMode_SS, Bool.false_eq_true, ↓reduceIte]

theorem dom_SS (m : Nat) : dom (.Psi (succM m) (succM m)) = .omega := by
  rw [dom_psi, cs_SS]
  have hr : (info (succM m)).seq.dom = .big (succM m) := by rw [info_seq_succM]; rfl
  have hl : ltB (succM m) (succM m) = false := by
    cases e : ltB (succM m) (succM m) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.irrefl _)
  simp only [SeqD.dom, hr, hl, Bool.false_eq_true, ↓reduceIte]


/-- 仮想的な塔の引数 `ψ₀ ⊕ g_k` は `M_m⁺` の列の項 -/
theorem virtE_eq_fundBig (m k : Nat) : virtE m k = fundBig (succM m) (virtG m k) := by
  show _ = (info (succM m)).seq.big (virtG m k)
  rw [info_seq_succM]
  rfl

/-- 仮想的な塔の引数の区間の下界：`LBI (ψ₀ ⊕ g_k) (ψ₀ ⊕ g_{k+1})` -/
theorem lbi_virtE {m : Nat} (hm : 1 ≤ m) (hS : BInv (succM m)) (hSS : BInv (.Psi (succM m) (succM m)))
    (k : Nat) : LBI (virtE m k) (virtE m (k + 1)) := by
  have hd : dom (succM m) = .big (succM m) := by
    show (info (succM m)).seq.dom = _
    rw [info_seq_succM]; rfl
  have hLg : LBI (virtG m k) (virtG m (k + 1)) := by
    cases k with
    | zero => exact lbi_zero _
    | succ k =>
      have h := hSS.om (dom_SS m) k
      rwa [fundNat_SS hm, fundNat_SS hm] at h
  have hadm : virtG m k = .zero ∨ (isPrincipal (virtG m k) = true ∧ Lt (base (succM m)) (virtG m k)) := by
    cases k with
    | zero => exact Or.inl rfl
    | succ k =>
      refine Or.inr ⟨rfl, ?_⟩
      show Lt (.Psi (succM m) .zero) (virtG m (k + 1))
      have h1 : virtG m 1 = .Psi (succM m) (virtE m 0) := rfl
      have hle : Le (virtG m 1) (virtG m (k + 1)) := seq_mono_le (virtG_F hm) (virtG_mono hm) (by omega)
      refine lt_of_lt_of_leY (wnf_psi0M hm) (virtG_F hm 1) (virtG_F hm _) ?_ hle
      rw [h1]
      exact lt_psi_psi_same.mpr (zero_lt (by show Tm.Psi (succM m) .zero ≠ .zero; intro e; cases e))
  have h := hS.big (succM m) hd (virtG m k) (virtG m (k + 1)) (virtG_F hm k) (virtG_F hm _)
    (Or.inr (virtG_mono hm k)) (virtG_lt _) hadm hLg
  rwa [← virtE_eq_fundBig, ← virtE_eq_fundBig] at h


/-- 和の加数は各部分の加数 -/
theorem mem_summands_oadd_cases {a y u : Tm} (ha : WNF a) (hy : WNF y) (hu : u ∈ summands (oadd a y)) :
    u ∈ summands a ∨ u ∈ summands y := by
  cases hs : summands y with
  | nil =>
    rw [eq_zero_of_summands_nil hs, oadd_zero] at hu
    exact Or.inl hu
  | cons h r =>
    rw [summands_oadd hs (nfl_principal (nfl_summands ha)) (nfl_principal (nfl_summands hy))] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact Or.inl ((List.takeWhile_sublist _).subset hu)
    · exact Or.inr (by rw [← hs]; exact hu)

/-- `Ψ_{M_m⁺}(a)` は `M_m` より大きい -/
theorem M_lt_psiS {m : Nat} (hm : 1 ≤ m) {a : Tm} (h : WNF (.Psi (succM m) a)) : Lt (.M m) (.Psi (succM m) a) :=
  coll_psiY h (WNF.M' hm) (inC_M m _ _) (M_lt_succM hm)

theorem fr_M_one {m : Nat} (hm : 1 ≤ m) : ∀ f, f ∈ fr (.M m) one → f = one := by
  intro f hf
  have h1M : Lt (Tm.Psi (.Om .zero) .zero) (.M m) := lt_of_lev_lt' (by show (1 : Nat) < m + 1; omega)
  simp only [one, fr, h1M, ↓reduceIte, List.mem_singleton] at hf
  exact hf

theorem fr_psiS {m : Nat} (hm : 1 ≤ m) {a : Tm} (h : WNF (.Psi (succM m) a)) :
    ∀ f, f ∈ fr (.M m) (.Psi (succM m) a) → f = one ∨ f ∈ fr (.M m) a := by
  intro f hf
  have hlt : ¬ Lt (.Psi (succM m) a) (.M m) := Lt.asymmY (WNF.M' hm) h (M_lt_psiS hm h)
  simp only [fr, hlt, ↓reduceIte, List.mem_append] at hf
  rcases hf with hf | hf
  · left
    simp only [succM, fr, List.nil_append] at hf
    exact fr_M_one hm f hf
  · exact Or.inr hf

/-- 仮想的な塔の引数の前線は `1` だけ -/
theorem fr_virtE {m : Nat} (hm : 1 ≤ m) : ∀ k f, f ∈ fr (.M m) (virtE m k) → f = one := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rcases fr_oadd_cases (wnf_psi0M hm) (virtG_F hm 0) hf with hf | hf
    · rcases fr_psiS hm (wnf_psi0M hm) f hf with e | hf
      · exact e
      · simp [fr] at hf
    · simp [virtG, fr] at hf
  | succ k ih =>
    intro f hf
    rcases fr_oadd_cases (wnf_psi0M hm) (virtG_F hm (k + 1)) hf with hf | hf
    · rcases fr_psiS hm (wnf_psi0M hm) f hf with e | hf
      · exact e
      · simp [fr] at hf
    · rcases fr_psiS hm (virtG_F hm (k + 1)) f hf with e | hf
      · exact e
      · exact ih f hf

/-- 仮想的な塔の引数の加数は `M_m` 以上 -/
theorem virtE_high {m : Nat} (hm : 1 ≤ m) (k : Nat) : ∀ u, u ∈ summands (virtE m k) → ¬ Lt u (.M m) := by
  intro u hu
  have hMF := WNF.M' hm
  rcases mem_summands_oadd_cases (wnf_psi0M hm) (virtG_F hm k) hu with hu | hu
  · rw [summands_principal rfl, List.mem_singleton] at hu
    rw [hu]
    exact Lt.asymmY hMF (wnf_psi0M hm) (M_lt_psiS hm (wnf_psi0M hm))
  · cases k with
    | zero => simp [virtG, summands] at hu
    | succ k =>
      rw [virtG_succ, summands_principal rfl, List.mem_singleton] at hu
      rw [hu]
      have hF := virtG_F hm (k + 1)
      rw [virtG_succ] at hF
      exact Lt.asymmY hMF hF (M_lt_psiS hm hF)


theorem ltB_S_rho {m : Nat} (hm : 1 ≤ m) (hρ : WNF (.Xi m (succM m))) :
    ltB (succM m) (.Xi m (succM m)) = false := by
  cases e : ltB (succM m) (.Xi m (succM m)) with
  | false => rfl
  | true =>
    exact absurd (ltB_iff.mp e) (Lt.asymmY hρ (WNF.succM hm)
      (lt_transY hρ (WNF.M' hm) (WNF.succM hm) (xi_lt_M _) (M_lt_succM hm)))

/-- 仮想的な塔の近似の項 -/
theorem app_S_nat {m : Nat} {P' : Tm} (hm : 1 ≤ m) (hρ : WNF (.Xi m (succM m))) (hPF : WNF P') (n : Nat) :
    (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq P' .zero).nat n =
      .Xi m (xa [] P' (virtE m n)) := by
  have hr : (info (succM m)).seq.dom = .big (succM m) := by rw [info_seq_succM]; rfl
  rw [app_xi_out_nat (succM_ne_M m) (succM_ne_xi m) hr (ltB_S_rho hm hρ), gam_xi_S hm, info_seq_succM]
  exact congrArg (Tm.Xi m) (combine_xi m [] hPF (virtE_F hm n))

theorem app_S_dom {m : Nat} {P' : Tm} (hm : 1 ≤ m) (hρ : WNF (.Xi m (succM m))) :
    (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq P' .zero).dom = .omega := by
  have hr : (info (succM m)).seq.dom = .big (succM m) := by rw [info_seq_succM]; rfl
  simp only [SeqD.dom, hr, ltB_S_rho hm hρ, Bool.false_eq_true, ↓reduceIte]

theorem nfl_S (m : Nat) (hm : 1 ≤ m) : NFL ([] ++ [succM m]) := nfl_of_wnf_principal (WNF.succM hm) rfl

theorem oadd_nil {x : Tm} (hx : WNF x) : oadd (ofSummands []) x = x := zero_oadd hx

/-- 仮想的な塔の引数は `C(g, d)` に入る（`0 < g`、それ以前の引数が `g` 未満） -/
theorem inC_virtE {m : Nat} (hm : 1 ≤ m) {g d : Tm} (h0 : Lt .zero g) (k : Nat)
    (h : ∀ j, j < k → Lt (virtE m j) g) : inC (virtE m k) g d = true :=
  inC_oadd (wnf_psi0M hm) (virtG_F hm _) (inC_psi0M h0) (inC_virtG hm h0 k h)

/-- 仮想的な塔（種なし）の梯子 -/
theorem seqLad_virt0 {m : Nat} (hm : 1 ≤ m) (hρ : WNF (.Xi m (succM m)))
    (hS : BInv (succM m)) (hSS : BInv (.Psi (succM m) (succM m)))
    (hSnat : ∀ n, WNF ((SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq
      .zero .zero).nat n)) :
    SeqLad (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq .zero .zero) := by
  refine ⟨fun _ n => ?_, fun σ hd => by rw [app_S_dom hm hρ] at hd; cases hd⟩
  have hy : ∀ k, WNF (.Xi m (oadd (ofSummands []) (virtE m k))) := fun k => by
    have := hSnat k
    rwa [app_S_nat hm hρ WNF.zero, xa_zero [] (virtE_F hm k)] at this
  rw [app_S_nat hm hρ WNF.zero n, app_S_nat hm hρ WNF.zero (n + 1), xa_zero [] (virtE_F hm n),
    xa_zero [] (virtE_F hm (n + 1))]
  have h0 : Lt .zero (virtE m (n + 1)) := lt_of_le_of_ltY WNF.zero (virtE_F hm n) (virtE_F hm _)
    (zero_le _) (virtE_mono hm n)
  refine lbi_app_step (nfl_S m hm) (virtE_F hm n) (virtE_F hm _) (Or.inr (virtE_mono hm n))
    (virtE_lt hm _) (lbi_virtE hm hS hSS n) (hy n) (hy (n + 1))
    (by rw [oadd_nil (virtE_F hm _)]; exact virtE_lt hm _) (fun d _ _ => ?_)
  rw [oadd_nil (virtE_F hm _)]
  exact inC_virtE hm h0 (n + 1) (fun j hj => virtE_lt_of hm hj)

/-- 仮想的な塔（種 `P'`）の梯子 -/
theorem seqLad_virtS {m : Nat} {P' B : Tm} (hm : 1 ≤ m) (hρ : WNF (.Xi m (succM m)))
    (SP : SeedPack m (succM m) P' B) (hSB : Le (succM m) B)
    (hS : BInv (succM m)) (hSS : BInv (.Psi (succM m) (succM m)))
    (hSnat : ∀ n, WNF ((SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq
      P' .zero).nat n)) :
    SeqLad (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq P' .zero) := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hPF := SP.F
  have hPp := SP.prin
  have hPρ := SP.ltρ
  have hρS : Lt (.Xi m (succM m)) (succM m) := lt_transY hρ hMF hSF (xi_lt_M _) (M_lt_succM hm)
  have hPS : Lt P' (succM m) := lt_transY hPF hρ hSF hPρ hρS
  have hPM : Lt P' (.M m) := lt_transY hPF hρ hMF hPρ (xi_lt_M _)
  have hHhi : ∀ k u, u ∈ summands (oadd (ofSummands []) (virtE m k)) → ¬ Lt u (.M m) := by
    intro k u hu
    rw [oadd_nil (virtE_F hm k)] at hu
    exact virtE_high hm k u hu
  have he : ∀ k, xa [] P' (virtE m k) = oadd (virtE m k) P' := fun k => by
    rw [xa_eq_high (nfl_S m hm) (virtE_F hm k) (virtE_lt hm k) hPF hPp hPM hMF (hHhi k),
      oadd_nil (virtE_F hm k)]
  have hA : ∀ k, WNF (oadd (virtE m k) P') := fun k => wnf_oadd (virtE_F hm k) hPF
  have hAS : ∀ k, Lt (oadd (virtE m k) P') (succM m) := fun k =>
    oadd_lt_prin (virtE_F hm k) hPF rfl (virtE_lt hm k) hPS
  have hy : ∀ k, WNF (.Xi m (oadd (virtE m k) P')) := fun k => by
    have := hSnat k
    rwa [app_S_nat hm hρ hPF, he k] at this
  have hfr : ∀ k f, f ∈ fr (.M m) (virtE m k) → Lt f P' := by
    intro k f hf
    rw [fr_virtE hm k f hf]
    exact SP.one
  have hhi : ∀ k u, u ∈ summands (virtE m k) → ¬ Lt u (.M m) := virtE_high hm
  refine ⟨fun _ n => ?_, fun σ hd => by rw [app_S_dom hm hρ] at hd; cases hd⟩
  rw [app_S_nat hm hρ hPF n, app_S_nat hm hρ hPF (n + 1), he n, he (n + 1)]
  -- 種から近似までの段
  have hPL : LBI P' (.Xi m (oadd (virtE m n) P')) := by
    refine SP.lad _ (hy n) (lt_of_lt_of_leY (hA n) hSF SP.BF (hAS n) hSB) ?_ (fun d hd hPd => ?_)
    · have hC : inC (oadd (virtE m n) P') (succM m) (.Xi m (succM m)) = true :=
        inC_oadd (virtE_F hm n) hPF
          (inC_virtE hm (zero_lt (by intro e; cases e)) n (fun j _ => virtE_lt hm j))
          (inC_of_lt_cut (Cut.of_wnf hρ) _ hPF hPρ)
      exact (lt_xi_xi0 (Lt.ne (hAS n))).mpr (Or.inl ⟨hAS n, hC⟩)
    · have hE0 : Lt .zero (virtE m n) :=
        lt_of_lt_of_leY WNF.zero (wnf_psi0M hm) (virtE_F hm n) (zero_lt (by intro e; cases e))
          (le_oadd_leftW (wnf_psi0M hm) (virtG_F hm n))
      have hEA : Le (virtE m n) (oadd (virtE m n) P') := le_oadd_leftW (virtE_F hm n) hPF
      have h0 : Lt .zero (oadd (virtE m n) P') :=
        lt_of_lt_of_leY WNF.zero (virtE_F hm n) (hA n) hE0 hEA
      exact inC_oadd (virtE_F hm n) hPF
        (inC_virtE hm h0 n (fun j hj => lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm n) (hA n)
          (virtE_lt_of hm hj) hEA))
        (inC_of_lt_cut (Cut.of_wnf hd) _ hPF hPd)
  exact lbi_seeded (virtE_F hm n) (virtE_F hm (n + 1)) hPF hPp SP.one hPM (hhi n) (hhi (n + 1))
    (Or.inr (virtE_mono hm n)) (lbi_virtE hm hS hSS n) (hy n) (hy (n + 1)) (hAS (n + 1)) SP.BF SP.closed
    (lt_of_lt_of_leY (hA _) hSF SP.BF (hAS (n + 1)) hSB) hPL (hfr n) (hfr (n + 1))


/-! ### 族の閉包の組み立て -/

/-- 加数の並びの先頭は全体以下 -/
theorem le_ofSummands_prefix {L S : List Tm} (h : NFL (L ++ S)) :
    Le (ofSummands L) (ofSummands (L ++ S)) := by
  rw [ofSummands_append h]
  exact le_oadd_leftW (wnf_ofSummands (nfl_append_left h)) (wnf_ofSummands (nfl_append_right h))

/-- `maxO` の場合分け（`p` が選ばれるなら `p` は `x` 未満でない）-/
theorem maxO_cases {P : Option Tm} {x : Tm} :
    maxO P x = x ∨ ∃ p, P = some p ∧ maxO P x = p ∧ ¬ ltB p x = true := by
  cases P with
  | none => exact Or.inl rfl
  | some p =>
    cases e : ltB p x with
    | true => left; simp [maxO, e]
    | false => right; exact ⟨p, rfl, by simp [maxO, e], by rw [e]; decide⟩

/-- 後者 `q` の族の閉包の梯子 -/
theorem seqLad_vk_succ {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true)
    (hRb : ∀ R, R ∈ summands q → BInv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hPs : ∀ p, P = some p → ¬ ltB p (.Xi m (predT q)) = true →
      ∃ B, SeedPack m q p B ∧ Le q B ∧ ∀ pre R rest, XG m q p pre rest R → SplitFr m q p pre R)
    (hSnat : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega → ∀ n,
      WNF ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ∧
      Lt ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ((mahloVK m q (info q).sums (.Xi m q) P).nat (n + 1))) :
    SeqLad (mahloVK m q (info q).sums (.Xi m q) P) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hq0 : q ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hpF := predT_WNF hqF hs
  have hpq := lt_predT hqF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hsp : summands (predT q) = ys := summands_predT hqF hys
  have hdl : (summands q).dropLast = ys := by rw [hys, List.dropLast_concat]
  have hyF := xi_pred_wnf hρ hs
  have hyρ := xi_pred_lt hρ hs
  have hqS : Le q (succM m) := le_of_ne_gtY hqF hSF hle
  obtain ⟨s, hs_def⟩ : ∃ s, s = maxO P (.Xi m (predT q)) := ⟨_, rfl⟩
  obtain ⟨hsF, -, -, -⟩ := maxO_spec (P := P) hyF (fun p hp => (hP p hp).1)
  rw [← hs_def] at hsF
  have hcase := maxO_cases (P := P) (x := .Xi m (predT q))
  rw [← hs_def] at hcase
  have hsρ : Lt s (.Xi m q) := by
    rcases hcase with e | ⟨p, hp, e, -⟩
    · rw [e]; exact hyρ
    · rw [e]; exact (hP p hp).2.1
  have hsp' : isPrincipal s = true := by
    rcases hcase with e | ⟨p, hp, e, -⟩
    · rw [e]; rfl
    · rw [e]; exact (hP p hp).2.2
  have hsM : Lt s (.M m) := lt_transY hsF hρ hMF hsρ hρM
  have hpred : pred q = predT q := rfl
  unfold mahloVK at hSnat ⊢
  rw [ite_eq_right hq0, ite_eq_left hs] at hSnat ⊢
  simp only [hpred, ← hs_def] at hSnat ⊢
  cases hsplit : splitPosD (.Xi m q) (info q).sums.dropLast with
  | none =>
    simp only [hsplit] at hSnat ⊢
    refine seqLad_tower hsF (Or.inr ?_)
    rcases hcase with e | ⟨p, hp, e, hnl⟩
    · rw [e]; rfl
    · obtain ⟨B, SP, -, -⟩ := hPs p hp hnl
      rw [e]; exact SP.of
  | some val =>
    obtain ⟨pre, R, r⟩ := val
    obtain ⟨rest, hsd, hr, hρR, hrest⟩ := splitPosD_spec hqF hρ hsplit
    subst hr
    have hsq : summands q = pre ++ R :: (rest ++ [one]) := by
      rw [hys, ← hdl, hsd]; simp
    have hRq : R ∈ summands q := by rw [hsq]; simp
    have hRW := summands_WNF q hqF R hRq
    have hsR : Lt s R := lt_of_lt_of_leY hsF hρ hRW.1 hsρ hρR
    simp only [hsplit, mkApp_xi (ltB_iff.mpr hsR)] at hSnat ⊢
    have G : XG m q s pre (rest ++ [one]) R := ⟨hρ, hsq, hsF, hsR, hsM, Or.inr hsp'⟩
    have hRS : R ≠ succM m := by
      intro e
      have hRp : Le R (predT q) := le_of_mem_summands hpF (by rw [hsp, ← hdl, hsd]; simp)
      rw [e] at hRp
      exact not_lt_of_leY hqF hSF hqS (lt_of_le_of_ltY hSF hpF hqF hRp hpq)
    have hpsum : summands (predT q) = pre ++ R :: rest := by rw [hsp, ← hdl, hsd]
    obtain ⟨B, SP, SF, hTB⟩ : ∃ B, SeedPack m q s B ∧ SplitFr m q s pre R ∧
        Le (ofSummands (pre ++ [R])) B := by
      have G' := G
      rcases hcase with e | ⟨p, hp, e, hnl⟩
      · rw [e] at G' ⊢
        have hW0 : predT q ≠ .zero := by
          intro e0; rw [e0] at hpsum; simp [summands] at hpsum
        refine ⟨_, seedPack_xi_pred hρ hs, (seedHull_xi_pred hρ hs hW0).splitFr G' (inv_of R hRW.1), ?_⟩
        have hN : NFL ((pre ++ [R]) ++ rest) := by
          rw [show (pre ++ [R]) ++ rest = pre ++ R :: rest by simp, ← hpsum]; exact nfl_summands hpF
        have := le_ofSummands_prefix hN
        rwa [show (pre ++ [R]) ++ rest = pre ++ R :: rest by simp, ← hpsum,
          ofSummands_summands _ hpF] at this
      · obtain ⟨B, SP, hqB, hSF⟩ := hPs p hp hnl
        rw [e] at G' ⊢
        exact ⟨B, SP, hSF pre R (rest ++ [one]) G', le_transY G.hTF hqF SP.BF G.hTq hqB⟩
    exact seqLad_app_seeded G SP SF hTB (inv_of R hRW.1) (hRb R hRq) hRS hSnat


/-- `R` の列を 1 つずらした近似は、元の近似の 1 つ先 -/
theorem app_shift_nat {τ R P c : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega) (n : Nat) :
    (SeqD.app τ (.xi m) pre R (.shift r) P c).nat n = (SeqD.app τ (.xi m) pre R r P c).nat (n + 1) := by
  simp only [SeqD.nat, SeqD.dom, hr]

theorem app_shift_dom {τ R P c : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega) :
    (SeqD.app τ (.xi m) pre R (.shift r) P c).dom = .omega := by
  simp only [SeqD.dom, hr]

/-- `app` の共終数は `ω` か正則項 -/
theorem app_dom_cases (τ R P c : Tm) (g : Gen) (pre : List Tm) (r : SeqD) :
    (SeqD.app τ g pre R r P c).dom = .omega ∨ ∃ σ, (SeqD.app τ g pre R r P c).dom = .big σ := by
  simp only [SeqD.dom]
  cases r.dom with
  | big σ =>
    dsimp only
    cases ltB σ τ
    · exact Or.inl rfl
    · exact Or.inr ⟨σ, rfl⟩
  | _ => exact Or.inl rfl

/-- 列の 0 番目は標準形 -/
theorem first_wnf {s : SeqD} (hd : s.dom = .omega ∨ ∃ σ, s.dom = .big σ)
    (hn : s.dom = .omega → ∀ n, WNF (s.nat n))
    (hb : ∀ σ, s.dom = .big σ → Lt .zero σ ∧ ∀ ξ, WNF ξ → Lt ξ σ → WNF (s.big ξ)) : WNF s.first := by
  unfold SeqD.first
  rcases hd with e | ⟨σ, e⟩
  · rw [e]; exact hn e 0
  · rw [e]; exact (hb σ e).2 .zero WNF.zero (hb σ e).1

/-- 極限 `q` の族の閉包の梯子 -/
theorem seqLad_vk_lim {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hq0 : q ≠ .zero) (hs : ¬ isSucc q = true)
    (hRb : ∀ R, R ∈ summands q → BInv R)
    (hSv : q = succM m → BInv (succM m) ∧ BInv (.Psi (succM m) (succM m)))
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hfr : ∀ f, f ∈ fr (.M m) q → ∃ p, P = some p ∧ Le f p)
    (hPeq : ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hPgt : ∀ p, P = some p → ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums)
        .zero .zero).first ≠ p → ∃ B, SeedPack m q p B ∧ Le q B ∧
          ∀ pre R rest, XG m q p pre rest R → (∀ u, u ∈ rest → Le u p) → R ≠ succM m →
            SplitFr m q p pre R)
    (hSnat : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega → ∀ n,
      WNF ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ∧
      Lt ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ((mahloVK m q (info q).sums (.Xi m q) P).nat (n + 1)))
    (hSbig : ∀ σ, (mahloVK m q (info q).sums (.Xi m q) P).dom = .big σ → Lt .zero σ ∧
      (∀ ξ, WNF ξ → Lt ξ σ → WNF ((mahloVK m q (info q).sums (.Xi m q) P).big ξ)) ∧
      ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
        Lt ((mahloVK m q (info q).sums (.Xi m q) P).big ξ) ((mahloVK m q (info q).sums (.Xi m q) P).big η)) :
    SeqLad (mahloVK m q (info q).sums (.Xi m q) P) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hqS : Le q (succM m) := le_of_ne_gtY hqF hSF hle
  have hne := summands_ne_nil hq0
  obtain ⟨R, hRdef⟩ : ∃ R, (summands q).getLast hne = R := ⟨_, rfl⟩
  have hpre : preT (info q).sums = (summands q).dropLast := preT_info q
  have hlast : lastT (info q).sums = R := by
    rw [lastT_info, List.getLast?_eq_some_getLast hne, hRdef]; rfl
  have hlastS : lastS (info q).sums = (info R).seq := by rw [lastS_coh (coh_sums q), hlast]
  have hsq : summands q = (summands q).dropLast ++ [R] := by
    rw [← hRdef]; exact (List.dropLast_concat_getLast hne).symm
  have hRq : R ∈ summands q := by rw [← hRdef]; exact List.getLast_mem hne
  have hRW := summands_WNF q hqF R hRq
  have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsq hRW.2]; exact hs
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hRi := inv_of R hRW.1
  -- `R = M_m⁺` なら `q = M_m⁺`
  have hqRS : ∀ R', R' ∈ summands q → R' = succM m → q = succM m := by
    intro R' hR'q e
    have hRle : Le R' q := le_of_mem_summands hqF hR'q
    rw [e] at hRle
    exact le_antisymmY hqF hSF hqS hRle
  unfold mahloVK at hSnat hSbig ⊢
  rw [ite_eq_right hq0, ite_eq_right hs] at hSnat hSbig ⊢
  simp only [hpre, hlast, hlastS] at hSnat hSbig hPeq hPgt ⊢
  -- 素の近似の梯子
  have hs0 : (∀ f, f ∈ fr (.M m) q →
      Lt f (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first) →
      ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).dom = .omega → ∀ n,
        WNF ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat n) ∧
        Lt ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat n)
          ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat (n + 1))) →
      (∀ σ, (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).dom = .big σ →
        ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
        Lt ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).big ξ)
          ((SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).big η)) →
      SeqLad (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero) := by
    intro hfront hn hb
    by_cases hRS : R = succM m
    · have hqS' := hqRS R hRq hRS
      obtain ⟨hS, hSS⟩ := hSv hqS'
      have hpre0 : (summands q).dropLast = [] := by
        rw [hqS']; rfl
      rw [hpre0] at hn ⊢
      subst hRS
      subst hqS'
      exact seqLad_virt0 hm hρ hS hSS (fun n => (hn (app_S_dom hm hρ) n).1)
    · exact seqLad_app_seedless G0 hRi (hRb R hRq) hRns hRS hfront hn hb
  cases P with
  | none =>
    exact hs0 (fun f hf => by obtain ⟨p, hp, -⟩ := hfr f hf; cases hp) hSnat
      (fun σ hd => (hSbig σ hd).2.2)
  | some p =>
    obtain ⟨hpF, hpρ, hpp⟩ := hP p rfl
    dsimp only at hSnat hSbig ⊢
    have hfront : ∀ f, f ∈ fr (.M m) q → Le f p := fun f hf => by
      obtain ⟨p', hp', hfp⟩ := hfr f hf; cases hp'; exact hfp
    by_cases h1 : ltB p (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first
      = true
    · rw [ite_eq_left h1] at hSnat hSbig ⊢
      have hfW := first_wnf (app_dom_cases _ _ _ _ _ _ _) (fun hd n => (hSnat hd n).1)
        (fun σ hd => ⟨(hSbig σ hd).1, (hSbig σ hd).2.1⟩)
      exact hs0 (fun f hf => lt_of_le_of_ltY (fr_elem hqF hf).1 hpF hfW (hfront f hf) (ltB_iff.mp h1))
        hSnat (fun σ hd => (hSbig σ hd).2.2)
    rw [ite_eq_right h1] at hSnat hSbig ⊢
    by_cases h2 : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first = p
    · -- 列を一つずらす
      rw [ite_eq_left h2] at hSnat hSbig ⊢
      have hRd : dom R = .omega := by
        have := hPeq p rfl h2
        exact this
      have hr : (info R).seq.dom = .omega := hRd
      refine ⟨fun hd n => ?_, fun σ hd => by rw [app_shift_dom hr] at hd; cases hd⟩
      have hsn := hSnat hd
      have hRN := hRi.1 hRd
      have hRP := hRN.props
      have hxF := hRP.nf
      have hnat0 : ∀ k, (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).nat k =
          .Xi m (xa (summands q).dropLast .zero (fundNat R k)) := fun k => app_xi_nat hr WNF.zero (hxF k)
      have hd0 : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).dom = .omega :=
        app_xi_dom_nat hr
      have hy : ∀ k, WNF (.Xi m (xa (summands q).dropLast .zero (fundNat R k))) := by
        intro k
        cases k with
        | zero =>
          have : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first =
              .Xi m (xa (summands q).dropLast .zero (fundNat R 0)) := by
            unfold SeqD.first; rw [hd0]; exact hnat0 0
          rw [← this, h2]; exact hpF
        | succ k =>
          have := (hsn k).1
          rw [app_shift_nat hr, hnat0] at this; exact this
      have hm01 : Lt (.Xi m (xa (summands q).dropLast .zero (fundNat R 0)))
          (.Xi m (xa (summands q).dropLast .zero (fundNat R 1))) := by
        have hxC := hRN.ub2 _ _ 0 (G0.hAF (hxF 1)) (G0.xa0 (hxF 1) (hRN.pos 1)) (Cut.of_wnf (hy 1))
          ((G0.parts (hxF 1) (hRP.lt 1) (xi_selfY (hy 1))).2.2)
        exact G0.lt2 (hxF 0) (hxF 1) (hRP.lt 1) (hRP.mono 0) (hy 1) hxC
      have hsm : ∀ k, Lt (.Xi m (xa (summands q).dropLast .zero (fundNat R (k + 1))))
          (.Xi m (xa (summands q).dropLast .zero (fundNat R (k + 1 + 1)))) := fun k => by
        have := (hsn k).2
        rw [app_shift_nat hr, app_shift_nat hr, hnat0, hnat0] at this; exact this
      have hmono : ∀ k, Le (.Xi m (xa (summands q).dropLast .zero (fundNat R 0)))
          (.Xi m (xa (summands q).dropLast .zero (fundNat R k))) := by
        intro k
        cases k with
        | zero => exact Or.inl rfl
        | succ k =>
          exact Or.inr (lt_of_lt_of_leY (hy 0) (hy 1) (hy _) hm01
            (seq_mono_le (y := fun j => .Xi m (xa (summands q).dropLast .zero (fundNat R (j + 1))))
              (fun j => hy (j + 1)) hsm (Nat.zero_le k)))
      have hfront' : ∀ f, f ∈ fr (.M m) q → Lt f (.Xi m (xa (summands q).dropLast .zero (fundNat R 0))) := by
        intro f hf
        have e0 : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first =
            .Xi m (xa (summands q).dropLast .zero (fundNat R 0)) := by
          unfold SeqD.first; rw [hd0]; exact hnat0 0
        rw [← e0, h2]
        rcases hfront f hf with e | h
        · exfalso
          have he_raw : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
              (lastS (info q).sums) .zero .zero).first = f := by
            rw [hpre, hlast, hlastS, h2]; exact e.symm
          exact floor_first_ne hρ hq0 hs (fun R hR => inv_of R (summands_WNF q hqF R hR).1)
            ((fr_rho_iff hρ).mpr hf) he_raw
        · exact h
      rw [app_shift_nat hr, app_shift_nat hr, hnat0, hnat0]
      exact lad_app0_nat G0 hRd hRN (hRb R hRq) hfront' hmono (n + 1)
    rw [ite_eq_right h2] at hSnat hSbig ⊢
    obtain ⟨B, SP, hqB, hSF⟩ := hPgt p rfl h1 h2
    cases hsg : splitGtD p (info q).sums with
    | none =>
      simp only [hsg] at hSnat hSbig ⊢
      exact seqLad_tower hpF (Or.inr SP.of)
    | some val =>
      obtain ⟨pre', R', r'⟩ := val
      obtain ⟨rest, hsq', hr', hpR', hrest'⟩ := splitGtD_spec hqF hpF hsg
      subst hr'
      have hR'q : R' ∈ summands q := by rw [hsq']; simp
      have hR'W := summands_WNF q hqF R' hR'q
      simp only [hsg, mkApp_xi (ltB_iff.mpr hpR')] at hSnat hSbig ⊢
      have G : XG m q p pre' rest R' :=
        ⟨hρ, hsq', hpF, hpR', lt_transY hpF hρ hMF hpρ hρM, Or.inr hpp⟩
      have hTB : Le (ofSummands (pre' ++ [R'])) B := le_transY G.hTF hqF SP.BF G.hTq hqB
      by_cases hRS : R' = succM m
      · have hqS' := hqRS R' hR'q hRS
        obtain ⟨hS, hSS⟩ := hSv hqS'
        subst hRS
        have hsum : summands q = [succM m] := by rw [hqS']; rfl
        have hpre0 : pre' = [] := by
          rw [hsum] at hsq'
          cases pre' with
          | nil => rfl
          | cons a l => simp at hsq'
        subst hpre0
        subst hqS'
        exact seqLad_virtS hm hρ SP hqB hS hSS (fun n => (hSnat (app_S_dom hm hρ) n).1)
      · exact seqLad_app_seeded G SP (hSF pre' R' rest G hrest' hRS) hTB (inv_of R' hR'W.1)
          (hRb R' hR'q) hRS hSnat


/-- `q = 0` の族の閉包（塔）の梯子 -/
theorem seqLad_vk_zero {m : Nat} {qs : DL} {ceil : Tm} {P : Option Tm}
    (hPF : ∀ p, P = some p → WNF p) (hP0 : ∀ p, P = some p → omegaFixed p = true) :
    SeqLad (mahloVK m .zero qs ceil P) := by
  unfold mahloVK
  rw [ite_eq_left rfl]
  have hfl : WNF (floorLev m) := wnf_kTerm (m - 1)
  obtain ⟨hGF, -, -, -⟩ := maxO_spec (P := P) hfl hPF
  refine seqLad_tower hGF ?_
  rcases maxO_cases (P := P) (x := floorLev m) with e | ⟨p, hp, e, -⟩
  · rw [e]
    unfold floorLev kTerm
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [e]; exact Or.inr (hP0 p hp)

/-- 族の閉包の梯子（種の性質を仮定して） -/
theorem seqLad_mahloVK {m : Nat} {q : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hRb : ∀ R, R ∈ summands q → BInv R)
    (hSv : q = succM m → BInv (succM m) ∧ BInv (.Psi (succM m) (succM m)))
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hP0 : q = .zero → ∀ p, P = some p → omegaFixed p = true)
    (hfr : ∀ f, f ∈ fr (.M m) q → ∃ p, P = some p ∧ Le f p)
    (hPs : isSucc q = true → ∀ p, P = some p → ¬ ltB p (.Xi m (predT q)) = true →
      ∃ B, SeedPack m q p B ∧ Le q B ∧ ∀ pre R rest, XG m q p pre rest R → SplitFr m q p pre R)
    (hPeq : q ≠ .zero → ¬ isSucc q = true → ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hPgt : q ≠ .zero → ¬ isSucc q = true → ∀ p, P = some p →
      ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
        (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums)
        .zero .zero).first ≠ p → ∃ B, SeedPack m q p B ∧ Le q B ∧
          ∀ pre R rest, XG m q p pre rest R → (∀ u, u ∈ rest → Le u p) → R ≠ succM m →
            SplitFr m q p pre R)
    (hSnat : (mahloVK m q (info q).sums (.Xi m q) P).dom = .omega → ∀ n,
      WNF ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ∧
      Lt ((mahloVK m q (info q).sums (.Xi m q) P).nat n) ((mahloVK m q (info q).sums (.Xi m q) P).nat (n + 1)))
    (hSbig : ∀ σ, (mahloVK m q (info q).sums (.Xi m q) P).dom = .big σ → Lt .zero σ ∧
      (∀ ξ, WNF ξ → Lt ξ σ → WNF ((mahloVK m q (info q).sums (.Xi m q) P).big ξ)) ∧
      ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
        Lt ((mahloVK m q (info q).sums (.Xi m q) P).big ξ) ((mahloVK m q (info q).sums (.Xi m q) P).big η)) :
    SeqLad (mahloVK m q (info q).sums (.Xi m q) P) := by
  by_cases hq0 : q = .zero
  · subst hq0
    exact seqLad_vk_zero (fun p hp => (hP p hp).1) (hP0 rfl)
  by_cases hs : isSucc q = true
  · exact seqLad_vk_succ hρ hs hRb hP (hPs hs) hSnat
  · exact seqLad_vk_lim hρ hq0 hs hRb hSv hP hfr (hPeq hq0 hs) (hPgt hq0 hs) hSnat hSbig

/-! ### `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）-/

/-- `M_m⁺` と `Ψ_{M_m⁺}(M_m⁺)` の梯子（`q = M_m⁺` の仮想的な塔に使う） -/
theorem binv_SS {m : Nat} (hm : 1 ≤ m) (hS : BInv (succM m)) : BInv (.Psi (succM m) (succM m)) := by
  have hSF := WNF.succM hm
  have hW : WNF (.Psi (succM m) (succM m)) :=
    WNF.mk_psi ⟨succM_tgt m, hSF, hSF, (fun _ _ e => by cases e), by
      show inC (.Om (.plus (.M m) one)) (succM m) (.Psi (succM m) (succM m)) = true
      rw [inC_om, inC_plus, inC_M, Bool.true_and]
      exact inC_one (by intro e; cases e)⟩
  exact binv_psi_diag_in hW (pre := []) (R := succM m) rfl (not_isSucc_succM m)
    (by show (info (succM m)).seq.dom = _; rw [info_seq_succM]; rfl) hS


/-- 族の閉包の項の性質（`t` の基本列の性質から）-/
theorem vk_props {t : Tm} {s : SeqD} (ht : WNF t) (hs : (info t).seq = s) :
    (s.dom = .omega → ∀ n, WNF (s.nat n) ∧ Lt (s.nat n) (s.nat (n + 1))) ∧
    (∀ σ, s.dom = .big σ → Lt .zero σ ∧ (∀ ξ, WNF ξ → Lt ξ σ → WNF (s.big ξ)) ∧
      ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt (s.big ξ) (s.big η)) := by
  have hP := props_all t ht
  refine ⟨fun hd n => ?_, fun σ hd => ?_⟩
  · have hd' : dom t = .omega := by show (info t).seq.dom = _; rw [hs]; exact hd
    have hN := hP.1 hd'
    have h1 := hN.nf n
    have h2 := hN.mono n
    simp only [fundNat, hs] at h1 h2
    exact ⟨h1, h2⟩
  · have hd' : dom t = .big σ := by show (info t).seq.dom = _; rw [hs]; exact hd
    have hB := hP.2 σ hd'
    refine ⟨hB.pos, fun ξ hξ hξσ => ?_, fun ξ η hξ hη hξη hησ => ?_⟩
    · have h1 := hB.nf ξ hξ hξσ
      simp only [fundBig, hs] at h1
      exact h1
    · have h2 := hB.mono ξ η hξ hη hξη hησ
      simp only [fundBig, hs] at h2
      exact h2

/-- 種 `Ψ_{Ξ_m(q)}(β)`（`q < β`、族について閉じた点）の上の族の閉包 `s` の梯子。`q` の加数と
（`q = M_m⁺` なら）`M_m⁺` の `BInv`、`s` の項の標準形と単調性を仮定する -/
theorem seqLad_mahloVK_psi {m : Nat} {q β : Tm} {s : SeqD} (hp : WNF (.Psi (.Xi m q) β)) (hqβ : Lt q β)
    (hs : s = mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) β)))
    (hRb : ∀ R, R ∈ summands q → BInv R) (hS : q = succM m → BInv (succM m))
    (hSnat : s.dom = .omega → ∀ n, WNF (s.nat n) ∧ Lt (s.nat n) (s.nat (n + 1)))
    (hSbig : ∀ σ, s.dom = .big σ → Lt .zero σ ∧ (∀ ξ, WNF ξ → Lt ξ σ → WNF (s.big ξ)) ∧
      ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt (s.big ξ) (s.big η)) :
    SeqLad s := by
  subst hs
  have hρ := hp.psi.piF
  have hm := hρ.xi.1
  have SP := seedPack_psi hp hqβ
  have SH := seedHull_psi hp hqβ
  refine seqLad_mahloVK hρ hRb (fun hqS => ⟨hS hqS, binv_SS hm (hS hqS)⟩) (fun p' hp' => ?_)
    (fun _ p' hp' => ?_) (fun f hf => ⟨_, rfl, SP.frq f hf⟩)
    (fun _ p' hp' _ => by
      cases hp'; exact ⟨_, SP, Or.inl rfl, fun pre R rest G => SH.splitFr G (inv_of R G.hRF)⟩)
    (fun _ _ p' hp' he => ?_)
    (fun _ _ p' hp' _ _ => by
      cases hp'; exact ⟨_, SP, Or.inl rfl, fun pre R rest G _ _ => SH.splitFr G (inv_of R G.hRF)⟩)
    hSnat hSbig
  · cases hp'; exact ⟨hp, lt_psi_targetY hp, rfl⟩
  · cases hp'; rfl
  · exfalso
    cases hp'
    obtain ⟨A, hA⟩ := app_xi_first (τ := .Xi m q) (m := m) (pre := preT (info q).sums)
      (R := lastT (info q).sums) (r := lastS (info q).sums) (P := .zero) (c := .zero)
    rw [hA] at he; cases he

/-- `Ψ_{Ξ_m(q)}(X'+1)`（`q < X'`）の梯子 -/
theorem binv_psi_succ_valid {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hqX : Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → BInv u) : BInv (.Psi (.Xi m q) X) := by
  have hP := ht.psi
  have hXF := hP.aF
  have hqF := hP.piF.xi.2.1
  have hpF : WNF (.Psi (.Xi m q) (predT X)) := psi_pred_wnf ht hs (fun n d e => by cases e; exact hqX)
  have hv : validR (.Xi m q) (pred X) = true := ltB_iff.mpr hqX
  have hcs := cs_succ_xi hXF hs hv
  have hpred : pred X = predT X := rfl
  rw [hpred] at hcs
  have hpr := vk_props ht (s := mahloVK m q (info q).sums (.Xi m q) (some (.Psi (.Xi m q) (predT X)))) hcs
  apply binv_of_seqLad
  show SeqLad (cs (.Xi m q) X)
  rw [hcs]
  refine seqLad_mahloVK_psi hpF hqX rfl (fun R hR => ih R ?_ (summands_WNF q hqF R hR).1)
    (fun hqS => ih (succM m) ?_ (by rw [← hqS]; exact hqF)) hpr.1 hpr.2
  · have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  · rw [← hqS]; simp only [Tm.size]; omega

end MahloOCF.FS
