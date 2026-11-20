import Mahlo.FS.FamVK

/-! 目標の族 `Ξ_m(q)` の閉包（`mahloVK`）の、共終数が正則項 `σ`（`σ < Ξ_m(q)`）の列の仕様 `FamBig`。

分ける加数 `R` の共終数が `σ` のとき、列は `y_ξ = Ξ_m(pre ⊕ (P' # R[ξ]))`（`ξ < σ`）。単調性には
`σ` の始点が列の下にあることが要り、`R[ξ] ∈ C(A_ξ, y_ξ)` の始点の証人（`BigInv.bw`、`M_m` 未満）から出す
（`famBig_xa`）。 -/

namespace MahloOCF.FS

open Tm

/-- `Ξ_m(q)` の族の閉包の、共終数 `σ` の列の性質（種 `P`） -/
structure FamBig (m : Nat) (q : Tm) (P : Option Tm) (σ : Tm) (y : Tm → Tm) : Prop where
  σF : WNF σ
  σreg : IsRegY σ
  σρ : Lt σ (.Xi m q)
  σsub : σ ∈ subs q
  σC : ∀ g d, Cut d → inC q g d = true → inC σ g d = true
  F : ∀ ξ, WNF ξ → Lt ξ σ → WNF (y ξ)
  xi : ∀ ξ, ∃ A, y ξ = .Xi m A
  mono : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt (y ξ) (y η)
  ltρ : ∀ ξ, WNF ξ → Lt ξ σ → Lt (y ξ) (.Xi m q)
  seed : ∀ p, P = some p → Lt p (y .zero)
  bot : Lt (floorLev m) (y .zero)
  ge : ∀ ξ, WNF ξ → Lt ξ σ → Lt ξ (y ξ)
  blt : ∀ ξ, WNF ξ → Lt ξ σ → Lt (base σ) (y ξ)
  clo : ∀ c ξ, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q → WNF ξ → Lt .zero ξ → Lt ξ σ →
    (∀ f, f ∈ lfr σ c → Lt f ξ) → (∀ w, w ∈ fr (.M m) c → Lt w (y ξ)) → Lt (.Xi m c) (y ξ)
  ub : ∀ g d ξ, WNF g → g ≠ .zero → Cut d → WNF ξ → Lt ξ σ → inC (base σ) g d = true →
    inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d → (∀ p, P = some p → inC p g d = true) →
    inC ξ g d = true → inC (y ξ) g d = true
  lo : ∀ g d ξ, Cut d → WNF ξ → Lt ξ σ → inC (y ξ) g d = true → inC ξ g d = true
  ub2 : ∀ g d ξ η, WNF g → g ≠ .zero → Cut d → WNF ξ → WNF η → Lt ξ η → Lt η σ →
    (inC (base σ) g d = true ∨ Le (base σ) ξ) → inC ξ g d = true → inC (y η) g d = true →
    inC (y ξ) g d = true
  bw : ∀ g d ξ L, Cut d → WNF ξ → Lt ξ σ → WNF L → Lt σ L → inC (y ξ) g d = true →
    ∃ u, WNF u ∧ inC u g d = true ∧ Le (base σ) u ∧ Lt u L

namespace FamBig

variable {m : Nat} {q σ : Tm} {P : Option Tm} {y : Tm → Tm}

theorem pos (F : FamBig m q P σ y) : Lt .zero σ := by
  refine zero_lt (fun e => ?_)
  have h := F.σreg
  rw [e] at h
  rcases h with h | ⟨c, h, -⟩ | ⟨n, h⟩ | ⟨n, p, h⟩ <;> cases h

theorem prin (F : FamBig m q P σ y) (ξ : Tm) : isPrincipal (y ξ) = true := by
  obtain ⟨A, hA⟩ := F.xi ξ; rw [hA]; rfl

theorem ne_zero (F : FamBig m q P σ y) (ξ : Tm) : y ξ ≠ .zero := by
  obtain ⟨A, hA⟩ := F.xi ξ; rw [hA]; intro e; cases e

theorem OF (F : FamBig m q P σ y) (ξ : Tm) : IsOF (y ξ) := by
  obtain ⟨A, hA⟩ := F.xi ξ; rw [hA]; exact Or.inl ⟨_, _, rfl⟩

theorem le0 (F : FamBig m q P σ y) {ξ : Tm} (hξ : WNF ξ) (hξσ : Lt ξ σ) : Le (y .zero) (y ξ) := by
  by_cases h0 : ξ = .zero
  · rw [h0]; exact Or.inl rfl
  · exact Or.inr (F.mono .zero ξ WNF.zero hξ (zero_lt h0) hξσ)

end FamBig

/-! ### 近似 `Ξ_m(pre ⊕ (P' # R[ξ]))` の列 -/

theorem app_xi_big_dom {τ R P' σ : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hr : r.dom = .big σ)
    (hστ : Lt σ τ) : (SeqD.app τ (.xi m) pre R r P' .zero).dom = .big σ := by
  simp only [SeqD.dom, hr, ltB_iff.mpr hστ, ↓reduceIte]

theorem app_xi_big {τ R P' : Tm} {m : Nat} {pre : List Tm} {r : SeqD} (hP' : WNF P') {ξ : Tm}
    (hx : WNF (r.big ξ)) :
    (SeqD.app τ (.xi m) pre R r P' .zero).big ξ = .Xi m (xa pre P' (r.big ξ)) := by
  simp only [SeqD.big, Gen.ap]
  rw [combine_xi m pre hP' hx]

/-- `R[ξ] ∈ C(pre ⊕ (P' # R[ξ]), M_m)`（`R` の共終数 `σ < M_m`） -/
theorem XG.big_inCM {m : Nat} {q P' R σ : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRi : BigInv R σ) (hσM : Lt σ (.M m)) {ξ : Tm} (hξ : WNF ξ) (hξσ : Lt ξ σ) :
    inC (fundBig R ξ) (xa pre P' (fundBig R ξ)) (.M m) = true := by
  have hRP := hRi.props
  have hσF := hRP.σF
  have hxF := hRP.nf ξ hξ hξσ
  by_cases h0 : fundBig R ξ = .zero
  · rw [h0]; exact inC_zero _ _
  have hcut := Cut.of_wnf G.hMF
  have hbF := wnf_base hσF hRi.σreg
  have hRC := G.pre_inC hxF (fun v hv hne hlt => hRi.gapP G.hRp ξ v hξ hξσ hv hne hlt)
    (hRi.pos ξ hξ hξσ) G.hqC R (by simp)
  exact hRi.ub _ _ ξ (G.hAF hxF) (G.xa0 hxF h0) hcut hξ hξσ
    (inC_of_lt_cut hcut _ hbF (lt_transY hbF hσF G.hMF (base_lt hσF hRi.σreg) hσM)) hRC
    (inC_of_lt_cut hcut _ hξ (lt_transY hξ hσF G.hMF hξσ hσM))

/-- 近似 `Ξ_m(pre ⊕ (P' # R[ξ]))` は標準形 -/
theorem XG.big_wnf {m : Nat} {q P' R σ : Tm} {pre rest : List Tm} (G : XG m q P' pre rest R)
    (hRi : BigInv R σ) (hσM : Lt σ (.M m)) {ξ : Tm} (hξ : WNF ξ) (hξσ : Lt ξ σ) :
    WNF (.Xi m (xa pre P' (fundBig R ξ))) :=
  G.nf (hRi.props.nf ξ hξ hξσ) (hRi.props.lt ξ hξ hξσ)
    (fun v hv hne hlt => hRi.gapP G.hRp ξ v hξ hξσ hv hne hlt) (hRi.pos ξ hξ hξσ)
    (G.big_inCM hRi hσM hξ hξσ)

/-- `R` の共終数が `σ < Ξ_m(q)` のときの近似 `Ξ_m(pre ⊕ (P' # R[ξ]))` の族の列 -/
theorem famBig_xa {m : Nat} {q P' R σ : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (hRi : BigInv R σ) (hσρ : Lt σ (.Xi m q))
    (hPρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) →
        Le (.Xi m c) P' ∨ Lt (.Xi m c) (.Xi m (xa pre P' (fundBig R .zero))))
    (hseed : ∀ p, P = some p → (WNF p ∧ Le p P') ∨ Lt p (.Xi m (xa pre P' (fundBig R .zero)))) :
    FamBig m q P σ (fun ξ => .Xi m (xa pre P' (fundBig R ξ))) := by
  have hMF := G.hMF
  have hqF := G.hqF
  have hρ := G.ht
  have hPF := G.hPF
  have hpreF := G.hpreF
  have hRP := hRi.props
  have hσF := hRP.σF
  have hσ0 := hRP.pos
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hσM : Lt σ (.M m) := lt_transY hσF hρ hMF hσρ hρM
  have hbF := wnf_base hσF hRi.σreg
  have hbσ := base_lt hσF hRi.σreg
  have hxF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (fundBig R ξ) := hRP.nf
  have hxR : ∀ ξ, WNF ξ → Lt ξ σ → Lt (fundBig R ξ) R := hRP.lt
  have hAF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (xa pre P' (fundBig R ξ)) := fun ξ hξ hξσ =>
    G.hAF (hxF ξ hξ hξσ)
  have hyF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (.Xi m (xa pre P' (fundBig R ξ))) := fun ξ hξ hξσ =>
    G.big_wnf hRi hσM hξ hξσ
  have hy0F := hyF .zero WNF.zero hσ0
  -- `R[ξ] ∈ C(A_ξ, y_ξ)`
  have hxCy : ∀ ξ, WNF ξ → Lt ξ σ →
      inC (fundBig R ξ) (xa pre P' (fundBig R ξ)) (.Xi m (xa pre P' (fundBig R ξ))) = true :=
    fun ξ hξ hξσ => (G.parts (hxF ξ hξ hξσ) (hxR ξ hξ hξσ) (xi_selfY (hyF ξ hξ hξσ))).2.2
  -- `ξ < y_ξ`
  have hge : ∀ ξ, WNF ξ → Lt ξ σ → Lt ξ (.Xi m (xa pre P' (fundBig R ξ))) := by
    intro ξ hξ hξσ
    have h1 := hRi.lo _ _ ξ (Cut.of_wnf (hyF ξ hξ hξσ)) hξ hξσ (hxCy ξ hξ hξσ)
    exact coll_xi0 (hyF ξ hξ hξσ) ξ hξ h1 (lt_transY hξ hσF hMF hξσ hσM)
  -- 種は近似未満
  have hP'y : ∀ ξ, WNF ξ → Lt ξ σ → Lt P' (.Xi m (xa pre P' (fundBig R ξ))) := fun ξ hξ hξσ =>
    G.seed_lt (hxF ξ hξ hξσ) (hxR ξ hξ hξσ) (hyF ξ hξ hξσ)
  -- `σ` の始点は近似未満（`R[ξ] ∈ C(A_ξ, y_ξ)` の始点の証人は `M_m` 未満なので `y_ξ` 未満）
  have hby : ∀ ξ, WNF ξ → Lt ξ σ → Lt (base σ) (.Xi m (xa pre P' (fundBig R ξ))) := by
    intro ξ hξ hξσ
    obtain ⟨u, huF, huC, hbu, huM⟩ := hRi.bw _ _ ξ (.M m) (Cut.of_wnf (hyF ξ hξ hξσ)) hξ hξσ hMF hσM
      (hxCy ξ hξ hξσ)
    exact lt_of_le_of_ltY hbF huF (hyF ξ hξ hξσ) hbu (coll_xi0 (hyF ξ hξ hξσ) u huF huC huM)
  -- 単調
  have hym : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
      Lt (.Xi m (xa pre P' (fundBig R ξ))) (.Xi m (xa pre P' (fundBig R η))) := by
    intro ξ η hξ hη hξη hησ
    have hξσ := lt_transY hξ hη hσF hξη hησ
    have hyη := hyF η hη hησ
    have hcut := Cut.of_wnf hyη
    have hx0 : fundBig R η ≠ .zero := by
      intro e
      have h := hRP.mono ξ η hξ hη hξη hησ
      rw [e] at h; exact not_lt_zero _ h
    have hC := hRi.ub2 _ _ ξ η (hAF η hη hησ) (G.xa0 (hxF η hη hησ) hx0) hcut hξ hη hξη hησ
      (Or.inl (inC_of_lt_cut hcut _ hbF (hby η hη hησ)))
      (inC_of_lt_cut hcut _ hξ (lt_transY hξ hη hyη hξη (hge η hη hησ))) (hxCy η hη hησ)
    exact G.lt2 (hxF ξ hξ hξσ) (hxF η hη hησ) (hxR η hη hησ) (hRP.mono ξ η hξ hη hξη hησ) hyη hC
  have hle0 : ∀ ξ, WNF ξ → Lt ξ σ →
      Le (.Xi m (xa pre P' (fundBig R .zero))) (.Xi m (xa pre P' (fundBig R ξ))) := by
    intro ξ hξ hξσ
    by_cases h0 : ξ = .zero
    · rw [h0]; exact Or.inl rfl
    · exact Or.inr (hym .zero ξ WNF.zero hξ (zero_lt h0) hξσ)
  have hRCρ : inC R q (.Xi m q) = true := G.pre_inCρ R (by simp)
  have hcutρ := Cut.of_wnf hρ
  have hxCρ : ∀ ξ, WNF ξ → Lt ξ σ → inC (fundBig R ξ) q (.Xi m q) = true := fun ξ hξ hξσ =>
    hRi.ub q _ ξ hqF G.hq0 hcutρ hξ hξσ
      (inC_of_lt_cut hcutρ _ hbF (lt_transY hbF hσF hρ hbσ hσρ)) hRCρ
      (inC_of_lt_cut hcutρ _ hξ (lt_transY hξ hσF hρ hξσ hσρ))
  refine {
    σF := hσF
    σreg := hRi.σreg
    σρ := hσρ
    σsub := subs_trans (mem_subs_of_mem_summands G.hRq) hRi.σsub
    σC := fun g d hd hqC => hRi.σC g d hd (inC_of_mem_summands hqF hqC G.hRq)
    F := hyF
    xi := fun ξ => ⟨_, rfl⟩
    mono := hym
    ltρ := fun ξ hξ hξσ => G.ltρ (hxF ξ hξ hξσ) (hxR ξ hξ hξσ) (hxCρ ξ hξ hξσ)
      (inC_of_lt_cut hcutρ _ hPF hPρ)
    seed := fun p hp => (hseed p hp).elim
      (fun h => lt_of_le_of_ltY h.1 hPF hy0F h.2 (hP'y .zero WNF.zero hσ0)) id
    bot := floorLev_lt_xi hy0F
    ge := hge
    blt := hby
    clo := fun c ξ hc hcρ hcq hξ hξ0 hξσ hlfr hfr => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hρC hρd hPC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => ?_
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => ?_
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => ?_ }
  · -- 族について閉じている
    have hcF := hc.xi.2.1
    have hyξ := hyF ξ hξ hξσ
    have hxξ := hxF ξ hξ hξσ
    have hx0 : fundBig R ξ ≠ .zero := by
      intro e
      have h := hRi.ge ξ hξ hξσ
      rw [e] at h
      rcases h with e' | h
      · rw [e'] at hξ0; exact Lt.irrefl _ hξ0
      · exact not_lt_zero _ h
    have hy0 : nsum P' (fundBig R ξ) ≠ .zero := by
      intro e
      have h1 := le_nsum_right hPF hxξ
      rw [e] at h1
      rcases h1 with e' | h1
      · exact hx0 e'
      · exact not_lt_zero _ h1
    by_cases hcT : Lt c (ofSummands (pre ++ [R]))
    · rcases lt_split G.hTF G.hsT hcF hcT with hle | ⟨c', hc', hc'0, hc'R, hsc, hce⟩
      · exact xi_step hc hyξ
          (lt_of_le_of_ltY hcF hpreF (hAF ξ hξ hξσ) hle (lt_oadd_left hpreF (G.hyF hxξ) hy0)) hfr
      · have h1 : Lt c' (fundBig R ξ) := hRi.lclo c' ξ hc' hc'R hξ hξ0 hξσ (fun f hf => by
          obtain ⟨g, hg, hfg⟩ := lfr_suffix hσF pre hcF hc' hc'0 hsc hf
          exact lt_of_le_of_ltY (hc'.of_mem_subs (lfr_spec hf).1) (hcF.of_mem_subs (lfr_spec hg).1)
            hξ hfg (hlfr g hg))
        refine xi_step hc hyξ ?_ hfr
        rw [hce]
        exact oadd_lt_oadd hpreF hc' (G.hyF hxξ)
          (lt_of_lt_of_leY hc' hxξ (G.hyF hxξ) h1 (le_nsum_right hPF hxξ))
    · rcases hrest c hc hcρ hcq hcT with h | h
      · exact lt_of_le_of_ltY hc hPF hyξ h (hP'y ξ hξ hξσ)
      · exact lt_of_lt_of_leY hc hy0F hyξ h (hle0 ξ hξ hξσ)
  · -- 上界
    by_cases hlt : Lt (.Xi m (xa pre P' (fundBig R ξ))) d
    · exact inC_of_lt_node (Or.inl ⟨_, _, rfl⟩) hlt
    rcases inC_xi_iff.mp hρC with h1 | ⟨hqC, hqg⟩
    · exact absurd h1 hρd
    have hRC := inC_of_mem_summands hqF hqC G.hRq
    have hxC := hRi.ub g d ξ hg hg0 hd hξ hξσ hbC hRC hξC
    refine inC_xi_iff.mpr (Or.inr ⟨G.inC_A (hxF ξ hξ hξσ) (fun s hs => ?_)
      (hP'ub g d hg hg0 hd hρC hρd hPC) hxC,
      lt_transY (hAF ξ hξ hξσ) hqF hg (G.hAq (hxF ξ hξ hξσ) (hxR ξ hξ hξσ)) hqg⟩)
    exact inC_of_mem_summands hqF hqC (G.hpreq hs)
  · -- 添字は列の項の成分
    by_cases hlt : Lt (.Xi m (xa pre P' (fundBig R ξ))) d
    · exact inC_of_lt_cut hd g hξ (hd _ _ hξ (hyF ξ hξ hξσ) (hge ξ hξ hξσ) hlt)
    rcases inC_xi_iff.mp hC with h1 | ⟨hAC, -⟩
    · exact absurd h1 hlt
    exact hRi.lo g d ξ hd hξ hξσ (G.parts (hxF ξ hξ hξσ) (hxR ξ hξ hξσ) hAC).2.2
  · -- 2 点の上界
    have hξσ := lt_transY hξ hη hσF hξη hησ
    by_cases hlt : Lt (.Xi m (xa pre P' (fundBig R η))) d
    · exact inC_of_lt_cut hd g (hyF ξ hξ hξσ) (hd _ _ (hyF ξ hξ hξσ) (hyF η hη hησ)
        (hym ξ η hξ hη hξη hησ) hlt)
    rcases inC_xi_iff.mp hC with h1 | ⟨hAC, hAg⟩
    · exact absurd h1 hlt
    obtain ⟨hpre, hP'C, hxC⟩ := G.parts (hxF η hη hησ) (hxR η hη hησ) hAC
    exact inC_xi_iff.mpr (Or.inr ⟨G.inC_A (hxF ξ hξ hξσ) hpre hP'C
      (hRi.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hxC),
      lt_transY (hAF ξ hξ hξσ) (hAF η hη hησ) hg
        (G.hAmono (hxF ξ hξ hξσ) (hxF η hη hησ) (hRP.mono ξ η hξ hη hξη hησ)) hAg⟩)
  · -- 始点の証人
    by_cases hlt : Lt (.Xi m (xa pre P' (fundBig R ξ))) d
    · exact ⟨base σ, hbF, inC_of_lt_cut hd g hbF (hd _ _ hbF (hyF ξ hξ hξσ) (hby ξ hξ hξσ) hlt),
        Or.inl rfl, lt_transY hbF hσF hL hbσ hσL⟩
    rcases inC_xi_iff.mp hC with h1 | ⟨hAC, -⟩
    · exact absurd h1 hlt
    exact hRi.bw g d ξ L hd hξ hξσ hL hσL (G.parts (hxF ξ hξ hξσ) (hxR ξ hξ hξσ) hAC).2.2

/-- 添字が `σ` 未満で一致する列に移す -/
theorem FamBig.congr {m : Nat} {q σ : Tm} {P : Option Tm} {y y' : Tm → Tm} (F : FamBig m q P σ y)
    (he : ∀ ξ, WNF ξ → Lt ξ σ → y' ξ = y ξ) (hxi : ∀ ξ, ∃ A, y' ξ = .Xi m A) :
    FamBig m q P σ y' := by
  have h0 := he .zero WNF.zero F.pos
  have hlt : ∀ {ξ η}, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt ξ σ := fun hξ hη hξη hησ =>
    lt_transY hξ hη F.σF hξη hησ
  refine {
    σF := F.σF
    σreg := F.σreg
    σρ := F.σρ
    σsub := F.σsub
    σC := F.σC
    F := fun ξ hξ hξσ => by rw [he ξ hξ hξσ]; exact F.F ξ hξ hξσ
    xi := hxi
    mono := fun ξ η hξ hη hξη hησ => by
      rw [he ξ hξ (hlt hξ hη hξη hησ), he η hη hησ]; exact F.mono ξ η hξ hη hξη hησ
    ltρ := fun ξ hξ hξσ => by rw [he ξ hξ hξσ]; exact F.ltρ ξ hξ hξσ
    seed := fun p hp => by rw [h0]; exact F.seed p hp
    bot := by rw [h0]; exact F.bot
    ge := fun ξ hξ hξσ => by rw [he ξ hξ hξσ]; exact F.ge ξ hξ hξσ
    blt := fun ξ hξ hξσ => by rw [he ξ hξ hξσ]; exact F.blt ξ hξ hξσ
    clo := fun c ξ hc hcρ hcq hξ hξ0 hξσ hlfr hfr => by
      rw [he ξ hξ hξσ] at hfr ⊢; exact F.clo c ξ hc hcρ hcq hξ hξ0 hξσ hlfr hfr
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hρC hρd hPC hξC => by
      rw [he ξ hξ hξσ]; exact F.ub g d ξ hg hg0 hd hξ hξσ hbC hρC hρd hPC hξC
    lo := fun g d ξ hd hξ hξσ hC => by
      rw [he ξ hξ hξσ] at hC; exact F.lo g d ξ hd hξ hξσ hC
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      rw [he η hη hησ] at hC
      rw [he ξ hξ (hlt hξ hη hξη hησ)]
      exact F.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [he ξ hξ hξσ] at hC; exact F.bw g d ξ L hd hξ hξσ hL hσL hC }

/-! ### `mahloVK` の分岐 -/

theorem app_xi_dom_big_inv {τ R P' σ : Tm} {m : Nat} {pre : List Tm} {r : SeqD}
    (h : (SeqD.app τ (.xi m) pre R r P' .zero).dom = .big σ) : r.dom = .big σ ∧ Lt σ τ := by
  cases hr : r.dom with
  | big σ' =>
    simp only [SeqD.dom, hr] at h
    cases hlt : ltB σ' τ with
    | true =>
      simp only [hlt, ↓reduceIte, Cof.big.injEq] at h
      subst h
      exact ⟨rfl, ltB_iff.mp hlt⟩
    | false => simp [hlt] at h
  | _ => simp [SeqD.dom, hr] at h

theorem tower_dom_ne_big (G σ : Tm) : (SeqD.tower G).dom ≠ .big σ := by
  simp [SeqD.dom]

/-- 加数 `R` での近似 `app` の、共終数が正則項 `σ` の列 -/
theorem famBig_app {m : Nat} {q P' R σ : Tm} {pre rest : List Tm} {P : Option Tm}
    (G : XG m q P' pre rest R) (hRi : Inv R)
    (hdom : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).dom = .big σ)
    (hPρ : Lt P' (.Xi m q))
    (hP'ub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC P' g d = true)
    (hrest : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands (pre ++ [R])) → Le (.Xi m c) P')
    (hseed : ∀ p, P = some p →
      (WNF p ∧ Le p P') ∨ Lt p (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first) :
    FamBig m q P σ (fun ξ => (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).big ξ) := by
  obtain ⟨hr, hσρ⟩ := app_xi_dom_big_inv hdom
  have hRd : dom R = .big σ := hr
  have hB := hRi.2 σ hRd
  have hfirst : (SeqD.app (.Xi m q) (.xi m) pre R (info R).seq P' .zero).first =
      .Xi m (xa pre P' (fundBig R .zero)) := by
    unfold SeqD.first; rw [hdom]
    exact app_xi_big G.hPF (hB.props.nf .zero WNF.zero hB.props.pos)
  have F := famBig_xa (P := P) G hB hσρ hPρ hP'ub
    (fun c h1 h2 h3 h4 => Or.inl (hrest c h1 h2 h3 h4))
    (fun p hp => (hseed p hp).imp id (fun h => by rw [hfirst] at h; exact h))
  exact F.congr (fun ξ hξ hξσ => app_xi_big G.hPF (hB.props.nf ξ hξ hξσ)) (fun ξ => ⟨_, rfl⟩)

/-! #### `q = q' + 1` -/

theorem famBig_vk_succ {m : Nat} {q σ : Tm} {P : Option Tm} (hρ : WNF (.Xi m q)) (hs : isSucc q = true)
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .big σ) :
    FamBig m q P σ (fun ξ => (mahloVK m q (info q).sums (.Xi m q) P).big ξ) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hq0 : q ≠ .zero := by intro e; rw [e] at hs; cases hs
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hpF := predT_WNF hqF hs
  have hpq := lt_predT hqF hs
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hsp : summands (predT q) = ys := summands_predT hqF hys
  have hdl : (summands q).dropLast = ys := by rw [hys, List.dropLast_concat]
  have hyF := xi_pred_wnf hρ hs
  have hyρ := xi_pred_lt hρ hs
  obtain ⟨s, hs_def⟩ : ∃ s, s = maxO P (.Xi m (predT q)) := ⟨_, rfl⟩
  obtain ⟨hsF, hys', hPs, hcase⟩ := maxO_spec (P := P) hyF (fun p hp => (hP p hp).1)
  rw [← hs_def] at hsF hys' hPs hcase
  have hsρ : Lt s (.Xi m q) := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; exact hyρ
    · rw [e]; exact (hP p hp).2.1
  have hsp' : isPrincipal s = true := by
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]; rfl
    · rw [e]; exact (hP p hp).2.2
  have hsM : Lt s (.M m) := lt_transY hsF hρ hMF hsρ hρM
  have hsC : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Xi m q) g d = true → ¬ Lt (.Xi m q) d →
      (∀ p, P = some p → inC p g d = true) → inC s g d = true := by
    intro g d hg _ _ hρC hρd hPC
    rcases hcase with e | ⟨p, hp, e⟩
    · rw [e]
      rcases inC_xi_iff.mp hρC with h1 | ⟨hqC', hqg⟩
      · exact absurd h1 hρd
      refine inC_xi_iff.mpr (Or.inr ⟨(inC_iff_summandsW hpF).mpr (fun u hu => ?_),
        lt_transY hpF hqF hg hpq hqg⟩)
      rw [hsp] at hu
      exact inC_of_mem_summands hqF hqC' (by rw [hys]; exact List.mem_append_left _ hu)
    · rw [e]; exact hPC p hp
  have hcl : ∀ c, WNF (.Xi m c) → Lt c q →
      (Lt c (predT q) → inC c (predT q) (.Xi m (predT q)) = true) → Le (.Xi m c) s := by
    intro c hc hcq hcC
    have hcF := hc.xi.2.1
    refine le_transY hc hyF hsF ?_ hys'
    rcases le_pred_of_lt_succ hqF hs hcF hcq with e | hlt
    · rw [e]; exact Or.inl rfl
    · exact Or.inr ((lt_xi_xi0 (Lt.ne hlt)).mpr (Or.inl ⟨hlt, hcC hlt⟩))
  have hpred : pred q = predT q := rfl
  unfold mahloVK at hdom ⊢
  rw [ite_eq_right hq0, ite_eq_left hs] at hdom ⊢
  simp only [hpred, ← hs_def] at hdom ⊢
  cases hsplit : splitPosD (.Xi m q) (info q).sums.dropLast with
  | none =>
    simp only [hsplit] at hdom
    exact absurd hdom (tower_dom_ne_big _ _)
  | some val =>
    obtain ⟨pre, R, r⟩ := val
    obtain ⟨rest, hsd, hr, hρR, hrest⟩ := splitPosD_spec hqF hρ hsplit
    subst hr
    have hsq : summands q = pre ++ R :: (rest ++ [one]) := by
      rw [hys, ← hdl, hsd]; simp
    have hRq : R ∈ summands q := by rw [hsq]; simp
    have hRW := summands_WNF q hqF R hRq
    have hsR : Lt s R := lt_of_lt_of_leY hsF hρ hRW.1 hsρ hρR
    simp only [hsplit, mkApp_xi (ltB_iff.mpr hsR)] at hdom ⊢
    have hRi := hRinv R hRq
    have G : XG m q s pre (rest ++ [one]) R :=
      ⟨hρ, hsq, hsF, hsR, hsM, Or.inr hsp'⟩
    have hpsum : summands (predT q) = pre ++ R :: rest := by rw [hsp, ← hdl, hsd]
    have hrest' : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
        ¬ Lt c (ofSummands (pre ++ [R])) → Le (.Xi m c) s := by
      intro c hc _ hcq hcT
      have hcF := hc.xi.2.1
      refine hcl c hc hcq (fun hlt => ?_)
      have h1 : cmpList (summands c) (pre ++ [R]) ≠ .lt := by
        intro h; apply hcT; unfold Lt; rw [cmp_eq, G.hsT]; exact h
      have h2 : cmpList (summands c) (pre ++ R :: (rest ++ [one])) = .lt := by
        have := hcq; unfold Lt at this; rw [cmp_eq, hsq] at this; exact this
      obtain ⟨l', hl'⟩ := prefix_of_between pre R (rest ++ [one]) (summands c) G.hN.1
        (nfl_summands hcF).1 h1 h2
      have hcp : summands c = (pre ++ [R]) ++ l' := by rw [hl']; simp
      have hpp : summands (predT q) = (pre ++ [R]) ++ rest := by rw [hpsum]; simp
      have htl := tail_le_of_lt hcF hpF hcp hpp hlt
      refine (inC_iff_summandsW hcF).mpr (fun u hu => ?_)
      rw [hcp] at hu
      rcases List.mem_append.mp hu with hu | hu
      · exact inC_of_mem_summands hpF (xi_selfY hyF) (by rw [hpp]; exact List.mem_append_left _ hu)
      · obtain ⟨v, hv, huv⟩ := htl u hu
        have hvp : v ∈ summands (predT q) := by rw [hpp]; exact List.mem_append_right _ hv
        have hvF := (summands_WNF _ hpF v hvp).1
        have huF := (summands_WNF c hcF u (by rw [hcp]; exact List.mem_append_right _ hu)).1
        have hvy : Lt v (.Xi m (predT q)) := coll_xi0 hyF v hvF
          (inC_of_mem_summands hpF (xi_selfY hyF) hvp) (lt_transY hvF hρ hMF (hrest v hv) hρM)
        exact inC_of_lt_cut (Cut.of_wnf hyF) _ huF (lt_of_le_of_ltY huF hvF hyF huv hvy)
    exact famBig_app G hRi hdom hsρ hsC hrest'
      (fun p hp => Or.inl ⟨(hP p hp).1, hPs p hp⟩)

/-! #### `q` 極限 -/

theorem famBig_vk_lim {m : Nat} {q σ : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hq0 : q ≠ .zero) (hs : ¬ isSucc q = true)
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hSeed : ∀ p, P = some p → ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first ≠ p → SeedHyp m q p)
    (hB5 : ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .big σ) :
    FamBig m q P σ (fun ξ => (mahloVK m q (info q).sums (.Xi m q) P).big ξ) := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
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
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hRi := hRinv R hRq
  have h0ρ : Lt .zero (.Xi m q) := zero_lt (by intro e; cases e)
  have hTq : ofSummands ((summands q).dropLast ++ [R]) = q := by
    rw [← hsq]; exact ofSummands_summands q hqF
  have hrest0 : ∀ c, WNF (.Xi m c) → Lt (.Xi m c) (.Xi m q) → Lt c q →
      ¬ Lt c (ofSummands ((summands q).dropLast ++ [R])) → Le (.Xi m c) .zero := by
    intro c _ _ hcq hcT
    rw [hTq] at hcT
    exact absurd hcq hcT
  unfold mahloVK at hdom ⊢
  rw [ite_eq_right hq0, ite_eq_right hs] at hdom ⊢
  simp only [hpre, hlast, hlastS] at hdom ⊢
  cases P with
  | none =>
    exact famBig_app G0 hRi hdom h0ρ (fun _ _ _ _ _ _ _ _ => inC_zero _ _) hrest0
      (fun p hp => nomatch hp)
  | some p =>
    obtain ⟨hpF, hpρ, hpp⟩ := hP p rfl
    dsimp only at hdom ⊢
    by_cases h1 : ltB p (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first
      = true
    · rw [ite_eq_left h1] at hdom ⊢
      exact famBig_app G0 hRi hdom h0ρ (fun _ _ _ _ _ _ _ _ => inC_zero _ _) hrest0
        (fun p' hp' => by cases hp'; exact Or.inr (ltB_iff.mp h1))
    rw [ite_eq_right h1] at hdom ⊢
    by_cases h2 : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (info R).seq .zero .zero).first = p
    · -- 列を一つずらす：`R` の列は `ω` 型
      exfalso
      rw [ite_eq_left h2] at hdom
      have hRd : dom R = .omega := by
        have := hB5 p rfl (by rw [hpre, hlast, hlastS]; exact h2)
        rwa [hlast] at this
      have hr : (info R).seq.dom = .omega := hRd
      have hd' : (SeqD.app (.Xi m q) (.xi m) (summands q).dropLast R (.shift (info R).seq) .zero .zero).dom
          = .omega := by simp only [SeqD.dom, hr]
      rw [hd'] at hdom; cases hdom
    rw [ite_eq_right h2] at hdom ⊢
    have hSp : SeedHyp m q p :=
      hSeed p rfl (by rw [hpre, hlast, hlastS]; exact h1) (by rw [hpre, hlast, hlastS]; exact h2)
    cases hsg : splitGtD p (info q).sums with
    | none =>
      simp only [hsg] at hdom
      exact absurd hdom (tower_dom_ne_big _ _)
    | some val =>
      obtain ⟨pre, R', r'⟩ := val
      obtain ⟨rest, hsq', hr', hpR', hrest'⟩ := splitGtD_spec hqF hpF hsg
      subst hr'
      have hR'q : R' ∈ summands q := by rw [hsq']; simp
      simp only [hsg, mkApp_xi (ltB_iff.mpr hpR')] at hdom ⊢
      have G : XG m q p pre rest R' :=
        ⟨hρ, hsq', hpF, hpR', lt_transY hpF hρ hMF hpρ hρM, Or.inr hpp⟩
      exact famBig_app G (hRinv R' hR'q) hdom hpρ (fun g d _ _ _ _ _ hPC => hPC p rfl)
        (fun c h1 h2 h3 h4 => hSp (pre ++ [R']) rest (by rw [hsq']; simp) hrest' c h1 h2 h3 h4)
        (fun p' hp' => by cases hp'; exact Or.inl ⟨hpF, Or.inl rfl⟩)

/-! ### まとめ -/

/-- 族の閉包 `mahloVK m q qs Ξ_m(q) P` の、共終数が正則項 `σ` の列の仕様 -/
theorem famBig_mahloVK {m : Nat} {q σ : Tm} {P : Option Tm} (hρ : WNF (.Xi m q))
    (hRinv : ∀ R, R ∈ summands q → Inv R)
    (hP : ∀ p, P = some p → WNF p ∧ Lt p (.Xi m q) ∧ isPrincipal p = true)
    (hSeed : ∀ p, P = some p → ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first = true →
      (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .zero).first ≠ p → SeedHyp m q p)
    (hB5 : ∀ p, P = some p → (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = p → dom (lastT (info q).sums) = .omega)
    (hdom : (mahloVK m q (info q).sums (.Xi m q) P).dom = .big σ) :
    FamBig m q P σ (fun ξ => (mahloVK m q (info q).sums (.Xi m q) P).big ξ) := by
  by_cases hq0 : q = .zero
  · subst hq0
    unfold mahloVK at hdom
    rw [ite_eq_left rfl] at hdom
    exact absurd hdom (tower_dom_ne_big _ _)
  by_cases hs : isSucc q = true
  · exact famBig_vk_succ hρ hs hRinv hP hdom
  · exact famBig_vk_lim hρ hq0 hs hRinv hP hSeed hB5 hdom

end MahloOCF.FS
