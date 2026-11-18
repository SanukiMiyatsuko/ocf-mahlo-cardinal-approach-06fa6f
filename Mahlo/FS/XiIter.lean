import Mahlo.FS.PsiAll

/-! `Ξ_m` の反復の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`（`R` の共終数は `M_m`）の閉包性。

`M_m` への対角化・`Ξ_m(q)` の族の閉包の両方で、添字の塔の共終性はこの形に帰着する。
`Y = pre ⊕ R` を段として作れる `M_m` 未満の項は塔の下にある（`xi_tower_hull`）。どの項を相手にするかは
述語 `Dm` で与える：`Dm` を満たす項は塔の下にあるか、成分に分解でき、`Ξ_m(ζ)` なら `ζ < Y`。 -/

namespace MahloOCF.FS

open Tm

/-- `Ξ_m(ζ) < Ξ_m(B)`：`ζ < B` で、`ζ` の `M_m` についての前線が `Ξ_m(B)` 未満 -/
theorem xi_step {m : Nat} {ζ B : Tm} (hz : WNF (.Xi m ζ)) (hy : WNF (.Xi m B)) (hζB : Lt ζ B)
    (hF : ∀ w, w ∈ fr (.M m) ζ → Lt w (.Xi m B)) : Lt (.Xi m ζ) (.Xi m B) := by
  obtain ⟨hm, hζF, -, hζC⟩ := hz.xi
  have hBF := hy.xi.2.1
  have hMF := WNF.M' hm
  refine (lt_xi_xi0 (fun e => Lt.ne hζB e)).mpr (Or.inl ⟨hζB, ?_⟩)
  exact inC_of_fr_lt hζF hMF hy hζF hBF hζC (Or.inr (xi_lt_M B)) (Or.inr hζB) hF

/-- `Ξ_m` の反復の塔の閉包性 -/
theorem xi_tower_hull {m : Nat} {Y R : Tm} {pre : List Tm} (hY : WNF Y)
    (hsY : summands Y = pre ++ [R]) (hRi : BigInv R (.M m))
    {γ : Nat → Tm} (hγF : ∀ k, WNF (γ k)) (hγM : ∀ k, Lt (γ k) (.M m))
    (hγm : ∀ k, Lt (γ k) (γ (k + 1)))
    (hγS : ∀ k, γ (k + 1) = .Xi m (oadd (ofSummands pre) (fundBig R (γ k))))
    (Dm : Tm → Prop) (hM : ∀ z, Dm z → Lt z (.M m))
    (hdec : ∀ z, WNF z → Dm z → (∃ k, Lt z (γ k)) ∨
      ((∀ a b, z = .plus a b → Dm a) ∧ (∀ e, z = .Om e → Dm e) ∧
       (∀ ρ a, z = .Psi ρ a → Dm ρ) ∧
       (∀ ζ, z = .Xi m ζ → Lt ζ Y ∧ ∀ w, w ∈ fr (.M m) ζ → Dm w))) :
    ∀ z, WNF z → Dm z → ∃ k, Lt z (γ k) := by
  have hXn : NFL (pre ++ [R]) := by rw [← hsY]; exact nfl_summands hY
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hRP := hRi.props
  have hOF : ∀ k, IsOF (γ (k + 1)) := fun k => by rw [hγS k]; exact Or.inl ⟨_, _, rfl⟩
  have hlev : ∀ k, lev (γ (k + 1)) = m := fun k => by rw [hγS k]; rfl
  have hm : 1 ≤ m := by have h := hγF 1; rw [hγS 0] at h; exact h.xi.1
  have hMF := WNF.M' hm
  have hxF : ∀ k, WNF (fundBig R (γ k)) := fun k => hRP.nf (γ k) (hγF k) (hγM k)
  have hγ0 : ∀ k, Lt .zero (γ (k + 1)) := fun k => zero_lt (hOF k).ne_zero
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hz hDz
  have hzM := hM z hDz
  rcases hdec z hz hDz with hk | ⟨hpl, hom, hps, hxi⟩
  · exact hk
  have hlz : lev z ≤ m := lev_le_of_lt_MY hm hz hzM
  rcases Nat.lt_or_eq_of_le hlz with hl | hl
  · exact ⟨1, lt_of_lev_lt' (by rw [hlev 0]; exact hl)⟩
  cases z with
  | zero => simp only [lev] at hl; exfalso; omega
  | M j =>
    exact ⟨1, bot_ltY rfl (by rw [hlev 0]; exact Nat.le_of_eq hl) (hOF 0).principal (hOF 0).not_bot
      (hγF 1)⟩
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hz.plus
    obtain ⟨k, hk⟩ := ih a (by simp only [Tm.size]; omega) ha (hpl a b rfl)
    exact ⟨k + 1, (lt_plus_prin_iffY hz (hOF k).principal).mpr
      (lt_transY ha (hγF k) (hγF (k + 1)) hk (hγm k))⟩
  | Om e =>
    have heF := hz.om.1
    obtain ⟨k, hk⟩ := ih e (by simp only [Tm.size]; omega) heF (hom e rfl)
    exact ⟨k + 1, (lt_om_OFG (hOF k) (hγF (k + 1))).mpr
      (lt_transY heF (hγF k) (hγF (k + 1)) hk (hγm k))⟩
  | Psi ρ a =>
    have hρF := hz.psi.piF
    obtain ⟨k, hk⟩ := ih ρ (by simp only [Tm.size]; omega) hρF (hps ρ a rfl)
    exact ⟨k, lt_transY hz hρF (hγF k) (lt_psi_targetY hz) hk⟩
  | Xi j ζ =>
    simp only [lev] at hl
    subst hl
    obtain ⟨hζY, hparts⟩ := hxi ζ rfl
    have hζF := hz.xi.2.1
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) hγF hγm (fr (.M j) ζ)
      (fun w hw => hζF.of_mem_subs (fr_spec hw).1)
      (fun w hw _ => ih w (by
          have := size_le_of_mem_subs (fr_spec hw).1
          simp only [Tm.size]; omega)
        (hζF.of_mem_subs (fr_spec hw).1) (hparts w hw))
    have hx0 : fundBig R (γ (N + 1)) ≠ .zero := by
      intro e
      have h1 := hRi.ge (γ (N + 1)) (hγF _) (hγM _)
      rw [e] at h1
      rcases h1 with e' | h1
      · exact (hOF N).ne_zero e'
      · exact not_lt_zero _ h1
    have hB : Lt ζ (oadd (ofSummands pre) (fundBig R (γ (N + 1)))) := by
      rcases lt_split hY hsY hζF hζY with hle | ⟨ζ', hζ', -, hζ'R, hsζ, hζe⟩
      · exact lt_of_le_of_ltY hζF hPF (wnf_oadd hPF (hxF _)) hle (lt_oadd_left hPF (hxF _) hx0)
      · rw [hζe]
        refine oadd_lt_oadd hPF hζ' (hxF _)
          (hRi.lclo ζ' (γ (N + 1)) hζ' hζ'R (hγF _) (hγ0 N) (hγM _) (fun g hg => ?_))
        have hgF := hζ'.of_mem_subs (lfr_spec hg).1
        have hy1 : WNF (Tm.Xi j (oadd (ofSummands pre) (fundBig R (γ N)))) := by
          rw [← hγS N]; exact hγF _
        have hCl : Cl (.M j) (γ (N + 1)) := by rw [hγS N]; exact Cl.of_xi hy1
        refine hCl g hgF (lfr_spec hg).2 (fun f hf => ?_)
        have hf1 : f ∈ fr (.M j) ζ' := fr_of_lfr hMF hζ' hg hf
        have hf2 : f ∈ fr (.M j) ζ :=
          fr_sub_of_summands (fun u hu => by rw [hsζ]; exact List.mem_append_right _ hu) hf1
        exact lt_transY (hζF.of_mem_subs (fr_spec hf2).1) (hγF N) (hγF _) (hN f hf2 trivial) (hγm N)
    have hy : WNF (Tm.Xi j (oadd (ofSummands pre) (fundBig R (γ (N + 1))))) := by
      rw [← hγS (N + 1)]; exact hγF _
    have hN2 : Lt (γ N) (Tm.Xi j (oadd (ofSummands pre) (fundBig R (γ (N + 1))))) := by
      rw [← hγS (N + 1)]
      exact lt_transY (hγF N) (hγF (N + 1)) (hγF (N + 1 + 1)) (hγm N) (hγm (N + 1))
    refine ⟨N + 1 + 1, ?_⟩
    rw [hγS (N + 1)]
    exact xi_step hz hy hB (fun w hw =>
      lt_transY (hζF.of_mem_subs (fr_spec hw).1) (hγF N) hy (hN w hw trivial) hN2)

/-- `Ψ_ρ(a) < M_m` なら `ρ < M_m` -/
theorem tgt_lt_M_of_psi {m : Nat} {ρ a : Tm} (hm : 1 ≤ m) (hz : WNF (.Psi ρ a)) (h : Lt (.Psi ρ a) (.M m)) :
    Lt ρ (.M m) :=
  (lt_M_iffY hz.psi.piF hm).mpr (by have := lev_le_of_lt_MY hm hz h; simpa [lev] using this)

/-- `Ξ_m` の反復の塔の閉包性（`C(Y, D)` 版）：段 `Y`・切断 `D` で作れる `M_m` 未満の項は、`D` 未満の項が
    塔の下にあれば塔の下 -/
theorem xi_tower_hull_C {m : Nat} {Y R D : Tm} {pre : List Tm} (hY : WNF Y)
    (hsY : summands Y = pre ++ [R]) (hRi : BigInv R (.M m))
    {γ : Nat → Tm} (hγF : ∀ k, WNF (γ k)) (hγM : ∀ k, Lt (γ k) (.M m))
    (hγm : ∀ k, Lt (γ k) (γ (k + 1)))
    (hγS : ∀ k, γ (k + 1) = .Xi m (oadd (ofSummands pre) (fundBig R (γ k))))
    (hDM : ∀ w, WNF w → Lt w D → Lt w (.M m))
    (hbase : ∀ z, WNF z → Lt z D → ∃ k, Lt z (γ k)) :
    ∀ z, WNF z → Lt z (.M m) → inC z Y D = true → ∃ k, Lt z (γ k) := by
  have hm : 1 ≤ m := by have h := hγF 1; rw [hγS 0] at h; exact h.xi.1
  have hMF := WNF.M' hm
  have H := xi_tower_hull hY hsY hRi hγF hγM hγm hγS (fun z => Lt z (.M m) ∧ inC z Y D = true)
    (fun z h => h.1) (fun z hz ⟨hzM, hzC⟩ => by
      by_cases hzD : Lt z D
      · exact Or.inl (hbase z hz hzD)
      refine Or.inr ⟨fun a b e => ?_, fun e e' => ?_, fun ρ a e => ?_, fun ζ e => ?_⟩
      · subst e
        rw [inC_plus, Bool.and_eq_true] at hzC
        exact ⟨lt_transY hz.plus.1 hz hMF (lt_plus_leftY hz) hzM, hzC.1⟩
      · subst e'
        rw [inC_om] at hzC
        exact ⟨lt_transY hz.om.1 hz hMF (lt_om_selfY hz) hzM, hzC⟩
      · subst e
        rcases inC_psi_iff.mp hzC with h | ⟨hρC, -, -⟩
        · exact absurd h hzD
        · exact ⟨tgt_lt_M_of_psi hm hz hzM, hρC⟩
      · subst e
        rcases inC_xi_iff.mp hzC with h | ⟨hζC, hζY⟩
        · exact absurd h hzD
        refine ⟨hζY, fun w hw => ⟨(fr_spec hw).2, ?_⟩⟩
        have hζF := hz.xi.2.1
        refine (inC_fr ζ hz.xi.2.2.2 (fun w' hw' h1 h2 => h1 (hDM w' (hζF.of_mem_subs hw') h2))
          (fun v hv hvζ => lt_transY (hζF.of_mem_subs hv) hζF hY hvζ hζY)).mp hζC w hw)
  exact fun z hz hzM hzC => H z hz ⟨hzM, hzC⟩

end MahloOCF.FS
