import Mahlo.FS.BachFr

/-! 底 `Ψ_{Ξ_m(q)}(q+1)` の梯子。種は目標の前線の最大元 `p`。`p` が素の近似の 0 番目より大きい場合、
`p = Ξ_m(b)`（`q < b`）か `p = Ψ_{Ξ_m(e)}(β)`（`q < e`）で、近似 `Ξ_m(pre ⊕ R[·] ⊕ p)` の前線は `p` 未満。 -/

namespace MahloOCF.FS

open Tm

/-! ### 底の種の形 -/

/-- 底の種の形：`q = pre ⊕ R`、`p` は `R` の中の `q` の前線の最大元で、素の近似の 0 番目 `Ξ_m(pre ⊕ x₀)` より
大きく、`R` の真の部分項で `R` 未満のものは `x₀` 未満、`p` の真の部分項で `p` 未満のものは 0 番目未満なら、
`p = Ξ_m(b)`（`q < b`）か `p = Ψ_{Ξ_m(e)}(β)`（`q < e`、`Ξ_m(q) < Ξ_m(e)`） -/
theorem floor_seed_form {m : Nat} {q p R x0 : Tm} {pre : List Tm} (hρ : WNF (.Xi m q))
    (hsq : summands q = pre ++ [R]) (hpq : p ∈ fr (.M m) q) (hpR : p ∈ subs R)
    (hmax : ∀ f, f ∈ fr (.M m) q → Le f p)
    (hx0 : WNF x0) (hx0R : Lt x0 R)
    (hyF : WNF (.Xi m (xa pre .zero x0))) (hlt : Lt (.Xi m (xa pre .zero x0)) p)
    (hgapR : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x0)
    (hgy : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v (.Xi m (xa pre .zero x0))) :
    (∃ b, p = .Xi m b ∧ Lt q b) ∨
      (∃ e β, p = .Psi (.Xi m e) β ∧ Lt q e ∧ Lt (.Xi m q) (.Xi m e)) := by
  have hqF := hρ.xi.2.1
  have hm := hρ.xi.1
  have hMF := WNF.M' hm
  have hqC := hρ.xi.2.2.2
  obtain ⟨hpF, hpM, -, -, -⟩ := fr_elem hqF hpq
  have hpρ : Lt p (.Xi m q) := k2xY hρ p hpq
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRW := summands_WNF q hqF R hRq
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero pre [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hAF := G0.hAF hx0
  have hpreF := G0.hpreF
  have hRsub : R ∈ subs q := mem_subs_of_mem_summands hRq
  have hOFy : IsOF (Tm.Xi m (xa pre .zero x0)) := Or.inl ⟨_, _, rfl⟩
  -- `A < pre ⊕ d'` なら `x0 < d'`
  have hcancel : ∀ d d', summands d = pre ++ summands d' → Lt (xa pre .zero x0) d → Lt x0 d' := by
    intro d d' hsd h
    have h1 : cmp (xa pre .zero x0) d = .lt := h
    rw [cmp_eq, G0.summands_xa hx0 hx0R, hsd, cmpList_append_same, zero_nsum _ hx0] at h1
    unfold Lt; rw [cmp_eq]; exact h1
  -- `(A, q)` に `R` の真の部分項はない
  have hmid : ∀ b, WNF b → b ∈ subs R → b ≠ R → Lt (xa pre .zero x0) b → Lt b q → False := by
    intro b hbF hbR hbne hAb hbq
    rcases lt_split hqF hsq hbF hbq with hle | ⟨b', hb', hb'0, hb'R, hsb, -⟩
    · exact not_lt_of_leY hbF hAF
        (le_transY hbF hpreF hAF hle (le_oadd_leftW hpreF (G0.hyF hx0))) hAb
    · have hx0b' := hcancel b b' hsb hAb
      have hb's : b' ∈ subs b := tail_mem_subs pre hbF hb' hb'0 hsb
      have hb'ne : b' ≠ R := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hb's)
        (size_lt_of_mem_subs_ne hbR hbne))
      exact Lt.asymmY hx0 hb' hx0b' (hgapR b' (subs_trans hbR hb's) hb'ne hb'R)
  have hlp : lev p = m := by
    have h1 : lev p ≤ m := by have := lev_le_of_lt_gen hpρ; simpa [lev] using this
    rcases Nat.lt_or_ge (lev p) m with h2 | h2
    · exact absurd hlt (Lt.asymmY hpF hyF (lt_of_lev_lt' (by simp only [lev]; exact h2)))
    · omega
  -- `q ∈ C(g, x)`（`q < g`、`p < x < M_m`）
  have hqCg : ∀ g x, WNF g → Lt q g → WNF x → Lt x (.M m) → Lt p x → inC q g x = true := by
    intro g x hg hqg hx hxM hpx
    refine (MahloOCF.inC_fr (R := .M m) (g0 := q) (g := g) (d := x) q hqC
      (fun w hw hwM hwx => hwM (lt_transY (hqF.of_mem_subs hw) hx hMF hwx hxM))
      (fun v hv hvq => lt_transY (hqF.of_mem_subs hv) hqF hg hvq hqg)).mpr (fun w hw => ?_)
    exact inC_of_lt_node (fr_node hw) (lt_of_le_of_ltY (fr_elem hqF hw).1 hpF hx (hmax w hw) hpx)
  rcases fr_node hpq with ⟨n, b, hpe⟩ | ⟨κ, β, hpe⟩
  · -- `p = Ξ_m(b)`
    have hn : n = m := by rw [hpe] at hlp; exact hlp
    rw [hn] at hpe
    subst hpe
    have hbF := hpF.xi.2.1
    have hbs : b ∈ subs R := subs_trans hpR (mem_subs_xi m b)
    have hbne : b ≠ R := ne_of_size_lt (Nat.lt_of_lt_of_le
      (by simp only [Tm.size]; omega : b.size < (Tm.Xi m b).size) (size_le_of_mem_subs hpR))
    have hAb : xa pre .zero x0 ≠ b := fun e => by rw [e] at hlt; exact Lt.irrefl _ hlt
    rcases (lt_xi_xi0 hAb).mp hlt with ⟨hAb', -⟩ | ⟨hbA, hbnC⟩
    · left
      refine ⟨b, rfl, ?_⟩
      rcases triY hqF hbF with h | e | h
      · exact h
      · exfalso; rw [e] at hpρ; exact Lt.irrefl _ hpρ
      · exact (hmid b hbF hbs hbne hAb' h).elim
    · exfalso
      have hbaseF : WNF (.Psi (.Xi m b) (sc b)) := wnf_base hpF (Or.inr (Or.inr (Or.inr ⟨m, b, rfl⟩)))
      obtain ⟨-, hbC⟩ := (baseOf_xi_iff m b _).mp (base_selfY hbaseF)
      have hbp : Lt (.Psi (.Xi m b) (sc b)) (.Xi m b) := lt_psi_targetY hbaseF
      have hC := inC_mono b b (.Psi (.Xi m b) (sc b)) (xa pre .zero x0) (.Xi m (xa pre .zero x0)) hbC
        (fun v hv hvx => hgy v (subs_trans (mem_subs_xi m b) hv)
          (ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hv) (by simp only [Tm.size]; omega)))
          (lt_transY (hbF.of_mem_subs hv) hbaseF hpF hvx hbp))
        (fun v hv hvb => lt_transY (hbF.of_mem_subs hv) hbF hAF hvb hbA)
      rw [hC] at hbnC; cases hbnC
  · -- `p = Ψ_κ(β)`
    subst hpe
    have hP := hpF.psi
    have hκF := hP.piF
    have hlκ : lev κ = m := hlp
    have hκp : Lt (.Psi κ β) κ := lt_psi_targetY hpF
    have hyκ : Lt (.Xi m (xa pre .zero x0)) κ := lt_transY hyF hpF hκF hlt hκp
    have hκs : κ ∈ subs R := subs_trans hpR (subs_psi_p (self_mem_subs κ))
    have hκsz : κ.size < (Tm.Xi m q).size := by
      have := size_le_of_mem_subs (subs_trans hRsub hκs)
      simp only [Tm.size]; omega
    -- 目標 `κ` は `Ξ_m(e)`
    obtain ⟨e, he⟩ : ∃ e, κ = .Xi m e := by
      rcases hP.tgt with h | ⟨c₀, h, hcs⟩ | ⟨n', e, h⟩
      · exfalso; subst h
        exact Lt.asymmY hyF hκF hyκ ((lt_om_OFG hOFy hyF).mpr (zero_lt (by intro e; cases e)))
      · exfalso; subst h
        have hc₀p : Lt c₀ (.Psi (.Om c₀) β) := cxY hpF hcs
        have hc₀s : c₀ ∈ subs (Tm.Psi (.Om c₀) β) := subs_psi_p (mem_subs_om c₀)
        exact Lt.asymmY hyF hκF hyκ ((lt_om_OFG hOFy hyF).mpr (hgy c₀ hc₀s (Lt.ne hc₀p) hc₀p))
      · have hn' : n' = m := by rw [h] at hlκ; exact hlκ
        exact ⟨e, by rw [h, hn']⟩
    subst he
    have heF := hκF.xi.2.1
    have hes : e ∈ subs R := subs_trans hκs (mem_subs_xi m e)
    have hene : e ≠ R := ne_of_size_lt (Nat.lt_of_lt_of_le
      (by simp only [Tm.size]; omega : e.size < (Tm.Psi (.Xi m e) β).size) (size_le_of_mem_subs hpR))
    obtain ⟨-, heC⟩ := (baseOf_xi_iff m e _).mp (base_selfY hpF)
    have hsz : ∀ v, v ∈ subs e → v ≠ Tm.Psi (.Xi m e) β := fun v hv => ne_of_size_lt (by
      have := size_le_of_mem_subs hv; simp only [Tm.size]; omega)
    have hAe : xa pre .zero x0 ≠ e := fun h => by rw [h] at hyκ; exact Lt.irrefl _ hyκ
    have hqe : Lt q e := by
      rcases (lt_xi_xi0 hAe).mp hyκ with ⟨hAe', -⟩ | ⟨heA, henC⟩
      · rcases triY heF hqF with h | h | h
        · exact (hmid e heF hes hene hAe' h).elim
        · exfalso; rw [h] at hκsz; simp only [Tm.size] at hκsz; omega
        · exact h
      · exfalso
        have := inC_mono_node e e (.Psi (.Xi m e) β) (xa pre .zero x0) (.Xi m (xa pre .zero x0))
          heC (fun v hv _ hvp => hgy v (subs_psi_p (subs_xi hv)) (hsz v hv) hvp)
          (fun v hv _ hvd => lt_transY (heF.of_mem_subs hv) heF hAF hvd heA)
        rw [this] at henC; cases henC
    have hqκ : inC q e (.Xi m e) = true := hqCg e (.Xi m e) heF hqe hκF (xi_lt_M e) hκp
    exact Or.inr ⟨e, β, rfl, hqe, (lt_xi_xi0 (Lt.ne hqe)).mpr (Or.inl ⟨hqe, hqκ⟩)⟩


/-! ### 底の種の性質 -/

/-- 底の種 `p`（目標の前線の最大元で、素の近似の 0 番目より大きい）：種の性質と、分割ごとの前線の評価 -/
theorem floor_pgt {m : Nat} {q : Tm} (hρ : WNF (.Xi m q)) (hq0 : q ≠ .zero) (hs : ¬ isSucc q = true)
    (p : Tm) (hp : maxL (frB (.Xi m q) (.Xi m q)) = some p)
    (h1 : ¬ ltB p (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums)
      (lastS (info q).sums) .zero .zero).first = true)
    (h2 : (SeqD.app (.Xi m q) (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums)
        .zero .zero).first ≠ p) :
    ∃ B, SeedPack m q p B ∧ Le q B ∧
      ∀ pre R rest, XG m q p pre rest R → (∀ u, u ∈ rest → Le u p) → R ≠ succM m →
        SplitFr m q p pre R := by
  obtain ⟨hm, hqF, hle, hqC⟩ := hρ.xi
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hρM : Lt (.Xi m q) (.M m) := xi_lt_M q
  have hqS' : Le q (succM m) := le_of_ne_gtY hqF hSF hle
  have hRinv : ∀ R, R ∈ summands q → Inv R := fun R hR => inv_of R (summands_WNF q hqF R hR).1
  have hpm : p ∈ fr (.Xi m q) (.Xi m q) := by rw [← frB_eq_fr]; exact maxL_mem hp
  have hpq : p ∈ fr (.M m) q := (fr_rho_iff hρ).mp hpm
  obtain ⟨hpF, hpρ, -, -, -⟩ := fr_elem hρ hpm
  have hpM : Lt p (.M m) := lt_transY hpF hρ hMF hpρ hρM
  have hmax : ∀ f, f ∈ fr (.M m) q → Le f p := fun f hf =>
    maxL_le (fun x hx => by rw [frB_eq_fr] at hx; exact (fr_elem hρ hx).1) hp f
      (by rw [frB_eq_fr]; exact (fr_rho_iff hρ).mpr hf)
  -- `q ≠ M_m⁺`（前線は `1` だけで、0 番目より小さい）
  have hqS : q ≠ succM m := by
    intro e
    subst e
    have hp1 : p = one := by
      have h' : p ∈ fr (.M m) one := by simpa only [succM, fr, List.nil_append] using hpq
      exact fr_M_one hm p h'
    apply h1
    have hdS := app_S_dom (P' := .zero) hm hρ
    have hfst : (SeqD.app (.Xi m (succM m)) (.xi m) [] (succM m) (info (succM m)).seq .zero .zero).first =
        .Xi m (virtE m 0) := by
      unfold SeqD.first; rw [hdS]
      rw [app_S_nat hm hρ WNF.zero 0, xa_zero [] (virtE_F hm 0), oadd_nil (virtE_F hm 0)]
    have hW : WNF (.Xi m (virtE m 0)) := by
      have h0 : Lt .zero (virtE m 0) := lt_of_lt_of_leY WNF.zero (wnf_psi0M hm) (virtE_F hm 0)
        (zero_lt (by intro e; cases e)) (le_oadd_leftW (wnf_psi0M hm) (virtG_F hm 0))
      exact WNF.mk_xi hm (virtE_F hm 0) (ne_gt_of_le (Or.inr (virtE_lt hm 0)))
        (inC_virtE hm h0 0 (fun j hj => absurd hj (Nat.not_lt_zero _)))
    have e1 : preT (info (succM m)).sums = [] := rfl
    have e2 : lastT (info (succM m)).sums = succM m := rfl
    have e3 : lastS (info (succM m)).sums = (info (succM m)).seq := rfl
    rw [e1, e2, e3, hfst, hp1]
    exact ltB_iff.mpr (one_lt_xi hW)
  obtain ⟨R, x0, hsq, hfirst, hx0, hx0R, hgap, -, -, hyF, hx0e⟩ := s0_first_xi hρ hq0 hs hqS hRinv
  rw [hfirst] at h1 h2
  have hlt : Lt (.Xi m (xa (summands q).dropLast .zero x0)) p := by
    rcases triY hyF hpF with h | e | h
    · exact h
    · exact absurd e h2
    · exact absurd (ltB_iff.mpr h) h1
  obtain ⟨hpR, hpleR, hpre⟩ := floor_tail hρ hsq hpm hx0 hx0R hyF hlt
  have hRq : R ∈ summands q := by rw [hsq]; simp
  have hRW := summands_WNF q hqF R hRq
  have hR0 : R ≠ .zero := by intro e; rw [e] at hRW; cases hRW.2
  have G0 : XG m q .zero (summands q).dropLast [] R :=
    ⟨hρ, hsq, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  have hA0e : xa (summands q).dropLast .zero x0 = oadd (ofSummands (summands q).dropLast) x0 :=
    xa_zero _ hx0
  have hfrA : ∀ f, f ∈ fr (.M m) (xa (summands q).dropLast .zero x0) →
      Lt f (.Xi m (xa (summands q).dropLast .zero x0)) := fun f hf => fr_lt_xi hyF hf
  have hfrpre : ∀ u f, u ∈ (summands q).dropLast → f ∈ fr (.M m) u →
      Lt f (.Xi m (xa (summands q).dropLast .zero x0)) := fun u f hu hf =>
    hfrA f (fr_of_mem_summands (G0.mem_xa_pre hx0 hx0R hu) hf)
  have hfrx0 : ∀ f, f ∈ fr (.M m) x0 → Lt f (.Xi m (xa (summands q).dropLast .zero x0)) :=
    fun f hf => hfrA f (by rw [hA0e]; exact fr_oadd_right G0.hpreF hx0 hf)
  have hp1 : Lt one p := lt_transY WNF.one hyF hpF (one_lt_xi hyF) hlt
  have hbot : Lt (floorLev m) p := lt_transY (wnf_kTerm _) hyF hpF (floorLev_lt_xi hyF) hlt
  have hRle : Le R q := le_of_mem_summands hqF hRq
  have hRS : Lt R (succM m) := by
    rcases le_transY hRW.1 hqF hSF hRle hqS' with e | h
    · exfalso; apply hqS
      exact le_antisymmY hqF hSF hqS' (by rw [← e]; exact hRle)
    · exact h
  have hRC : inC R (succM m) (.M m) = true :=
    inC_mono R q (.M m) (succM m) (.M m) (inC_of_mem_summands hqF hqC hRq) (fun _ _ h => h)
      (fun v hv hvq => lt_of_lt_of_leY (hRW.1.of_mem_subs hv) hqF hSF hvq hqS')
  have hfrR : ∀ f, f ∈ fr (.M m) R → Le f p := fun f hf => hmax f (fr_of_mem_summands hRq hf)
  have hfrR0 : ∀ f, f ∈ fr (.M m) (fund R .zero) →
      Lt f (.Xi m (xa (summands q).dropLast .zero x0)) := by
    rw [← hx0e]; exact hfrx0
  -- `p` の真の部分項で `p` 未満のものは 0 番目未満
  have hgy : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v (.Xi m (xa (summands q).dropLast .zero x0)) := by
    rcases hpleR with hRp | hpR'
    · intro v hv hne hvp
      rw [hRp] at hv hne hvp
      have hx0y : Lt x0 (.Xi m (xa (summands q).dropLast .zero x0)) :=
        coll_xi0 hyF x0 hx0 (G0.parts hx0 hx0R (xi_selfY hyF)).2.2
          (lt_transY hx0 hRW.1 hMF hx0R (by rw [← hRp]; exact hpM))
      exact lt_transY (hRW.1.of_mem_subs hv) hx0 hyF (hgap v hv hne hvp) hx0y
    · exact (fr_fs_low hm hpF hp1 R hRW.1 hRS hRC hpR hfrR).c _ hyF hfrR0
  have hform := floor_seed_form hρ hsq hpq (fr_spec hpR).1 hmax hx0 hx0R hyF hlt hgap hgy
  have hOF : IsOF p := by
    rcases hform with ⟨b, rfl, -⟩ | ⟨e, β, rfl, -, -⟩
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩
  have hlp : lev p = m := by
    rcases hform with ⟨b, rfl, -⟩ | ⟨e, β, rfl, -, -⟩ <;> rfl
  -- 分割の加数
  have hD : ∀ u, u ∈ summands q → u = R ∨ u ∈ (summands q).dropLast := fun u hu => by
    rw [hsq] at hu
    rcases List.mem_append.mp hu with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_singleton.mp h)
  have hsplit : ∀ pre R' rest, XG m q p pre rest R' → (∀ u, u ∈ pre ++ [R'] → Lt p u) ∧
      (∀ u, u ∈ pre ++ [R'] → u ∈ summands q) := by
    intro pre R' rest G
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rcases List.mem_append.mp hu with hu | hu
      · have huW := G.hNT.1 u (List.mem_append_left _ hu)
        have hR'u : Le R' u := le_of_ne_gtY G.hRF huW.1 (nfl_append_ge G.hNT u hu R' (by simp))
        exact lt_of_lt_of_leY hpF G.hRF huW.1 G.hPR hR'u
      · rw [List.mem_singleton.mp hu]; exact G.hPR
    · rw [G.hsum]
      rcases List.mem_append.mp hu with hu | hu
      · exact List.mem_append_left _ hu
      · rw [List.mem_singleton.mp hu]; simp
  -- 分割の前線の評価（`R = p` なら包 `C(g, p)`、`p < R` なら構造的な評価）
  have hSplit : ∀ (g : Tm), WNF g → g ≠ .zero → Lt q g →
      (∀ z, WNF z → inC z g p = true → inC z q (.Xi m q) = true → Lt z (.M m) → Lt z p) →
      ∀ pre R' rest, XG m q p pre rest R' → (∀ u, u ∈ rest → Le u p) → R' ≠ succM m →
        SplitFr m q p pre R' := by
    intro g hgF hg0 hqg hcoll pre R' rest G hrest _
    obtain ⟨hgt, hinq⟩ := hsplit pre R' rest G
    rcases hpleR with hRp | hpR'
    · refine splitFr_of_hull G hgF hg0 (fun s hs => ?_) hcoll (inv_of R' G.hRF)
      have hsq' := hinq s hs
      have hsD : s ∈ (summands q).dropLast := by
        rcases hD s hsq' with e | h
        · exfalso
          have h' := hgt s hs
          rw [e, ← hRp] at h'
          exact Lt.irrefl _ h'
        · exact h
      have hsF := (summands_WNF q hqF s hsq').1
      refine (MahloOCF.inC_fr (R := .M m) (g0 := q) (g := g) (d := p) s
        (inC_of_mem_summands hqF hqC hsq')
        (fun w hw hwM hwp => hwM (lt_transY (hsF.of_mem_subs hw) hpF hMF hwp hpM))
        (fun v hv hvq => lt_transY (hsF.of_mem_subs hv) hqF hgF hvq hqg)).mpr (fun w hw => ?_)
      exact inC_of_lt_node (fr_node hw)
        (lt_transY (fr_elem hsF hw).1 hyF hpF (hfrpre s w hsD hw) hlt)
    · have hrest0 : rest = [] := by
        cases rest with
        | nil => rfl
        | cons u r =>
          exfalso
          have hu : u ∈ summands q := by rw [G.hsum]; simp
          have hpu : Lt p u := by
            rcases hD u hu with e | h
            · rw [e]; exact hpR'
            · exact hpre u h
          exact not_lt_of_leY (summands_WNF q hqF u hu).1 hpF (hrest u (by simp)) hpu
      subst hrest0
      have hLL : pre ++ [R'] = (summands q).dropLast ++ [R] := by rw [← hsq, G.hsum]
      obtain ⟨hpreD, hR'R⟩ := List.append_inj' hLL rfl
      have hR'R' : R' = R := by simpa using hR'R
      subst hR'R'
      subst hpreD
      have SL := fr_fs_low hm hpF hp1 R' hRW.1 hRS hRC hpR hfrR
      have h0 : ∀ f, f ∈ fr (.M m) (fund R' .zero) → Lt f p := fun f hf =>
        lt_transY (fr_elem (wnf_f0 hRW.1) hf).1 hyF hpF (hfrR0 f hf) hlt
      have hab := SL.ab h0
      have hpreF := G.hpreF
      have hfrpre' : ∀ f, f ∈ fr (.M m) (ofSummands (summands q).dropLast) → Lt f p := fun f hf => by
        obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
        rw [summands_ofSummands _ (nfl_principal (nfl_append_left G.hNT))] at hu
        exact lt_transY (fr_elem hpreF hf).1 hyF hpF (hfrpre u f hu hfu) hlt
      refine ⟨fun hRM => SL.dd hRM (fun e => by rw [e] at hpR'; exact Lt.irrefl _ hpR') hOF hlp hbot h0,
        fun hd n f hf => ?_, fun σ hd _ => ⟨(hab.2 σ hd).1, fun ξ hξ hξσ f hf => ?_⟩⟩
      · rcases fr_oadd_cases hpreF (((props_all R' hRW.1).1 hd).nf n) hf with hf | hf
        · exact hfrpre' f hf
        · exact hab.1 hd n f hf
      · rcases fr_oadd_cases hpreF (((props_all R' hRW.1).2 σ hd).nf ξ hξ hξσ) hf with hf | hf
        · exact hfrpre' f hf
        · exact (hab.2 σ hd).2 ξ hξ hξσ f hf
  rcases hform with ⟨b, rfl, hqb⟩ | ⟨e, β, rfl, hqe, hρκ⟩
  · have hbF := hpF.xi.2.1
    have hb0 : b ≠ .zero := by intro h; rw [h] at hqb; exact not_lt_zero _ hqb
    exact ⟨b, ⟨hpF, rfl, hp1, hpρ, rfl, hbot, hbF, xiClosed_xi hpF,
        fun A hA hAb _ hC => lbi_xi_inv_hull hpF hA hAb (fun d hd hpd => hC d hd hpd), hmax⟩,
      Or.inr hqb, hSplit b hbF hb0 hqb (fun z hz hzg _ hzM => coll_xi0 hpF z hz hzg hzM)⟩
  · have hκF := hpF.psi.piF
    have heF := hκF.xi.2.1
    have hβF := hpF.psi.aF
    have heβ : Lt e β := hpF.psi.act m e rfl
    have hβ0 : β ≠ .zero := by intro h; rw [h] at heβ; exact not_lt_zero _ heβ
    exact ⟨e, ⟨hpF, rfl, hp1, hpρ, rfl, hbot, heF, xiClosed_psi hpF heβ,
        fun A hA _ hAρ hC => lbi_psi_seed_hull hpF hA (lt_transY hA hρ hκF hAρ hρκ) hC, hmax⟩,
      Or.inr hqe, hSplit β hβF hβ0 (lt_transY hqF heF hβF hqe heβ)
        (fun z hz hzg hzq hzM =>
          coll_psiY hpF hz hzg (lt_transY hz hρ hκF (coll_xi0 hρ z hz hzq hzM) hρκ))⟩

/-! ### `Ψ_{Ξ_m(q)}(q+1)`（底）-/

/-- 底 `Ψ_{Ξ_m(q)}(X)`（`X = q + 1`）の梯子 -/
theorem binv_psi_succ_floor {m : Nat} {q X : Tm} (ht : WNF (.Psi (.Xi m q) X))
    (hs : isSucc X = true) (hnv : ¬ Lt q (predT X))
    (ih : ∀ u, u.size < (Tm.Psi (.Xi m q) X).size → WNF u → BInv u) : BInv (.Psi (.Xi m q) X) := by
  have hP := ht.psi
  have hρ := hP.piF
  have hXF := hP.aF
  obtain ⟨hm, hqF, -, -⟩ := hρ.xi
  have hv : validR (.Xi m q) (pred X) = false := by
    cases e : validR (.Xi m q) (pred X) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) hnv
  have hcs := cs_succ_xi_floor hXF hs hv
  have hRinv : ∀ R, R ∈ summands q → Inv R := fun R hR => inv_of R (summands_WNF q hqF R hR).1
  have hRb : ∀ R, R ∈ summands q → BInv R := fun R hR => by
    refine ih R ?_ (summands_WNF q hqF R hR).1
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hR)
    simp only [Tm.size]; omega
  have hpm : ∀ p, maxL (frB (.Xi m q) (.Xi m q)) = some p → p ∈ fr (.Xi m q) (.Xi m q) :=
    fun p hp => by rw [← frB_eq_fr]; exact maxL_mem hp
  have hpr := vk_props ht (s := mahloVK m q (info q).sums (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))) hcs
  apply binv_of_seqLad
  show SeqLad (cs (.Xi m q) X)
  rw [hcs]
  refine seqLad_mahloVK hρ hRb (fun hqS => ?_) (front_max_spec hρ) (fun hq0 p hp => ?_)
    (fun f hf => ?_) (fun hsq p hp hnl => ?_)
    (fun hq0 hsq p hp he => (floor_first_ne hρ hq0 hsq hRinv (hpm p hp) he).elim)
    (fun hq0 hsq p hp h1 h2 => floor_pgt hρ hq0 hsq p hp h1 h2) hpr.1 hpr.2
  · have hS : BInv (succM m) := by
      refine ih (succM m) ?_ (by rw [← hqS]; exact hqF)
      rw [← hqS]; simp only [Tm.size]; omega
    exact ⟨hS, binv_SS hm hS⟩
  · exfalso
    subst hq0
    have h := (fr_rho_iff hρ).mp (hpm p hp)
    simp [fr] at h
  · have hf' : f ∈ frB (.Xi m q) (.Xi m q) := by rw [frB_eq_fr]; exact (fr_rho_iff hρ).mpr hf
    cases hP0 : maxL (frB (.Xi m q) (.Xi m q)) with
    | none => rw [maxL_none hP0] at hf'; cases hf'
    | some p =>
      exact ⟨p, rfl, maxL_le (fun x hx => by rw [frB_eq_fr] at hx; exact (fr_elem hρ hx).1) hP0 f hf'⟩
  · exfalso
    apply hnl
    have hyF := xi_pred_wnf hρ hsq
    obtain ⟨ys, hys⟩ := summands_of_isSucc hsq
    have hpq := (fr_rho_iff hρ).mp (hpm p hp)
    obtain ⟨u, hu, hpu⟩ := mem_fr_iff.mp hpq
    rw [hys] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ltB_iff.mpr (fr_lt_xi hyF (mem_fr_iff.mpr ⟨u, by rw [summands_predT hqF hys]; exact hu, hpu⟩))
    · rw [List.mem_singleton.mp hu] at hpu
      rw [fr_M_one hm p hpu]; exact ltB_iff.mpr (one_lt_xi hyF)

/-- `Ξ_n(p)` への崩壊で引数が後者の場合の梯子 -/
theorem psiXiSuccBInv : PsiXiSuccBInv := by
  intro n p X ht hs ih
  by_cases h : Lt p (predT X)
  · exact binv_psi_succ_valid ht hs h ih
  · exact binv_psi_succ_floor ht hs h ih

end MahloOCF.FS
