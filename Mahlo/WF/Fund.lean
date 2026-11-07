import Mahlo.WF.Wmax

/-! 後続基数への崩壊の基本列の構文的な証明（大基数の仮定も `Classical.choice` も使わない）。

`Ψ_π(b+1)`（`π = Ω_0` か `Ω_{c'+1}`）が標準形なら

* `Ψ_π(b)` は標準形（`psi_pred_WNF`）。
* `Ψ_π(b+1)` 未満の主要項は `Ψ_π(b)` 以下（`prin_le_psi_pred`）。
* したがって `Ψ_π(b)·(n+1)`（`fsTermY`）は標準形で狭義増加し、`Ψ_π(b+1)` 未満で、`Ψ_π(b+1)` 未満の
  標準形はどれかの `Ψ_π(b)·(n+1)` 未満（`fs_psi_succY`）。

`Ψ_π(b)` が標準形であること（`b ∈ C(b, Ψ_π(b))`）は、`b` の部分項の節点 `v` について
「`v < Ψ_π(b+1)` なら `v < Ψ_π(b)`」を `v` の大きさについての帰納法で示して導く（`Ψ_π(b)` 自身は `b` の
部分項にならないので、比較の規則だけで計算できる）。 -/

namespace MahloOCF

open Tm

/-- `Ψ_π(b)·(n+1)` -/
def fsTermY (pi b : Tm) (n : Nat) : Tm := ofSummands (List.replicate (n + 1) (.Psi pi b))

/-- 崩壊の節点 -/
def IsNode (v : Tm) : Prop := (∃ m a, v = .Xi m a) ∨ (∃ p a, v = .Psi p a)

/-- `inC_mono` の精密版：比較の仮定は節点だけ、段の仮定は真の部分項だけ -/
theorem inC_mono_node : ∀ w g d g' d' : Tm, inC w g d = true →
    (∀ v, v ∈ subs w → IsNode v → Lt v d → Lt v d') →
    (∀ v, v ∈ subs w → v.size < w.size → Lt v g → Lt v g') →
    inC w g' d' = true := by
  intro w
  induction w with
  | zero => intros; exact inC_zero _ _
  | M n => intros; exact inC_M n _ _
  | plus a b iha ihb =>
    intro g d g' d' h hd hg
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨iha g d g' d' h.1 (fun v hv => hd v (subs_plus_l hv))
        (fun v hv hs => hg v (subs_plus_l hv) (by simp only [Tm.size]; omega)),
      ihb g d g' d' h.2 (fun v hv => hd v (subs_plus_r hv))
        (fun v hv hs => hg v (subs_plus_r hv) (by simp only [Tm.size]; omega))⟩
  | Om e ihe =>
    intro g d g' d' h hd hg
    rw [inC_om] at h ⊢
    exact ihe g d g' d' h (fun v hv => hd v (subs_om hv))
      (fun v hv hs => hg v (subs_om hv) (by simp only [Tm.size]; omega))
  | Xi n a iha =>
    intro g d g' d' h hd hg
    rcases inC_xi_iff.mp h with h | ⟨h1, h2⟩
    · exact inC_xi_iff.mpr (Or.inl (hd _ (self_mem_subs _) (Or.inl ⟨n, a, rfl⟩) h))
    · exact inC_xi_iff.mpr (Or.inr ⟨iha g d g' d' h1 (fun v hv => hd v (subs_xi hv))
        (fun v hv hs => hg v (subs_xi hv) (by simp only [Tm.size]; omega)),
        hg a (mem_subs_xi n a) (by simp only [Tm.size]; omega) h2⟩)
  | Psi k δ ihk ihδ =>
    intro g d g' d' h hd hg
    rcases inC_psi_iff.mp h with h | ⟨hk, hδ, hlt⟩
    · exact inC_psi_iff.mpr (Or.inl (hd _ (self_mem_subs _) (Or.inr ⟨k, δ, rfl⟩) h))
    · refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, hg δ (mem_subs_psi_a k δ)
        (by simp only [Tm.size]; omega) hlt⟩)
      · exact ihk g d g' d' hk (fun v hv => hd v (subs_psi_p hv))
          (fun v hv hs => hg v (subs_psi_p hv) (by simp only [Tm.size]; omega))
      · exact ihδ g d g' d' hδ (fun v hv => hd v (subs_psi_a hv))
          (fun v hv hs => hg v (subs_psi_a hv) (by simp only [Tm.size]; omega))

/-- `inC` は加数ごと -/
theorem inC_iff_summands : ∀ (x g d : Tm), inC x g d = true ↔ ∀ s, s ∈ summands x → inC s g d = true
  | .zero, g, d => by simp [summands, inC_zero]
  | .plus a b, g, d => by
    rw [inC_plus, Bool.and_eq_true, summands_plus, inC_iff_summands b g d]
    simp only [List.mem_cons, forall_eq_or_imp]
  | .M _, _, _ | .Om _, _, _ | .Xi _ _, _, _ | .Psi _ _, _, _ => by
    simp only [summands, List.mem_singleton, forall_eq]

/-- `M_m` は階 `m + 1` 以上の `Ψ` より小さい -/
theorem M_lt_psi {m : Nat} {π β : Tm} (hl : m + 1 ≤ lev π) : Lt (.M m) (.Psi π β) := by
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · exact (lt_principal_iff rfl rfl).mpr (cmpP_M_psi hl).1

theorem kTerm_lt_psi {m : Nat} {π β : Tm} (hm : 1 ≤ m) (hl : lev π = m) :
    Lt (kTerm (m - 1)) (.Psi π β) := by
  unfold kTerm
  split
  · exact zero_lt (by intro e; cases e)
  · exact M_lt_psi (by omega)

/-- `baseOf_om_psiOm` の、`Ψ_{Ω_d}(β)` が標準形であることを仮定しない形 -/
theorem baseOf_om_psiOm' {c d β : Tm} (hc : WNF c) (hs : isSucc c = true) (hdF : WNF d)
    (hcd : cmp c d ≠ .gt)
    (hKL : ∀ X, IsOF X → X ∈ summands c → Lt X d → Lt X (.Psi (.Om d) β)) :
    baseOf (.Om c) (.Psi (.Om d) β) = true := by
  rw [baseOf_om_succ hs]
  have hζd : Lt (predT c) d := (lt_predT_iff hc hs hdF).mpr hcd
  unfold omOf
  split
  · rename_i hfix
    have hζF := predT_WNF hc hs
    rcases fixed_shape hζF hfix with ⟨m, hm⟩ | hX
    · rw [hm]
      obtain ⟨ys, hys⟩ := summands_of_isSucc hs
      have h1 := summands_predT hc hys
      rw [hm] at h1
      have hys' : ys = [.M m] := h1.symm
      subst hys'
      have hlc : lev (.M m) = lev c := lev_head (rest := [one]) hys
      have hle : lev c ≤ lev d := lev_le_of_cmp_ne_gt hcd
      exact M_lt_psi (by simp only [lev] at hlc ⊢; omega)
    · exact hKL _ hX (predT_mem_summands hc hs (fixed_principal hfix)) hζd
  · exact lt_om_psiOmG.mpr hζd

/-- `c = b + 1` -/
theorem succT_predT {c : Tm} (hc : WNF c) (hs : isSucc c = true) : succT (predT c) = c := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  exact eq_of_summands_eq (succT_WNF (predT_WNF hc hs)) hc
    (by rw [summands_succT, summands_predT hc hys, hys])

/-- `v < b + 1`、`v ≠ b` なら `v < b` -/
theorem lt_pred_of_lt_succ {c v : Tm} (hc : WNF c) (hs : isSucc c = true) (hv : WNF v)
    (h : Lt v c) (hne : v ≠ predT c) : Lt v (predT c) := by
  have hbF := predT_WNF hc hs
  rcases triY hv hbF with h' | e | h'
  · exact h'
  · exact absurd e hne
  · have := succT_leY hbF hv h'
    rw [succT_predT hc hs] at this
    exact absurd h (not_lt_of_leY hc hv this)

/-- `v < b + 1` なら `v ≤ b` -/
theorem le_pred_of_lt_succ {c v : Tm} (hc : WNF c) (hs : isSucc c = true) (hv : WNF v)
    (h : Lt v c) : Le v (predT c) := by
  by_cases e : v = predT c
  · exact Or.inl e
  · exact Or.inr (lt_pred_of_lt_succ hc hs hv h e)

section
variable {d c : Tm} (h : WNF (.Psi (.Om d) c)) (hc : isSucc c = true)
include h hc

/-- `b` の部分項の節点 `v` について、`v < Ψ_{Ω_d}(b+1)` なら `v < Ψ_{Ω_d}(b)` -/
theorem node_lt_psi_pred : ∀ v, v ∈ subs (predT c) → IsNode v →
    Lt v (.Psi (.Om d) c) → Lt v (.Psi (.Om d) (predT c)) := by
  have hcF := h.psi.aF
  have hbF := predT_WNF hcF hc
  have hπF := h.psi.piF
  have hdF := hπF.om.1
  have G := goodYL (wnf_list2 h hbF)
  have hS : ∀ {v}, v ∈ subs (predT c) → v ∈ subsL [.Psi (.Om d) c, predT c] := fun hv =>
    mem_subsL.mpr ⟨_, by simp, hv⟩
  have htS : Tm.Psi (.Om d) c ∈ subsL [.Psi (.Om d) c, predT c] := memL
  have hπS : Tm.Om d ∈ subsL [.Psi (.Om d) c, predT c] := mem_subsL.mpr ⟨_, by simp, mem_subs_psi_p _ c⟩
  intro v
  induction v using size_induction with
  | h v ih =>
  intro hv hnode hvt
  have hvS := hS hv
  have hvF := G.nf v hvS
  have hlv : lev v ≤ lev (Tm.Om d) := (lev_le_of_lt_gen hvt : lev v ≤ lev (Tm.Psi (.Om d) c))
  rcases Nat.lt_or_eq_of_le hlv with hl | hl
  · exact lt_of_lev_lt' hl
  have hsub : ∀ {u}, u ∈ subs v → u ∈ subs (predT c) := fun hu => subs_trans hv hu
  rcases hnode with ⟨m, f, rfl⟩ | ⟨κ, β, rfl⟩
  · -- `v = Ξ_m(f)`
    simp only [lev] at hl
    have hm := hvF.xi.1
    obtain ⟨hgt, hbt⟩ := (lt_xi_psi_iff (π := .Om d) (γ := c) (f := f) (n := m) hl.symm).mp hvt
    refine (lt_xi_psi_iff (π := .Om d) (γ := predT c) (f := f) (n := m) hl.symm).mpr ⟨hgt,
      (baseOf_xi_iff m f _).mpr ⟨kTerm_lt_psi hm hl.symm, ?_⟩⟩
    refine inC_mono_node f f _ f _ ((baseOf_xi_iff m f _).mp hbt).2 (fun u hu hun hut => ?_)
      (fun _ _ _ h => h)
    have := size_le_of_mem_subs hu
    exact ih u (by simp only [Tm.size]; omega) (hsub (subs_xi hu)) hun hut
  · -- `v = Ψ_κ(β)`
    simp only [lev] at hl
    have hκS := G.sub hvS (mem_subs_psi_p κ β)
    rcases G.tri hκS hπS with hκπ | rfl | hπκ
    · have hne : κ ≠ .Om d := fun e => Lt.ne hκπ e
      have hnlt := G.asymm hκS hπS hκπ
      have hbt := (lt_psi_psi_ltT (κ := κ) (β := β) (π := .Om d) (γ := c) hl hne hnlt).mp hvt
      refine (lt_psi_psi_ltT (κ := κ) (β := β) (π := .Om d) (γ := predT c) hl hne hnlt).mpr ?_
      rcases hvF.psi_shape with rfl | ⟨d', rfl, hs'⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hd'S := G.sub hκS (mem_subs_om d')
        refine baseOf_om_psiOm' (G.nf _ hd'S) hs' hdF (ne_gt_of_le (Or.inr (lt_om_iffG.mp hκπ)))
          (fun X hX hXm hXd => ?_)
        have hXsub : X ∈ subs d' := mem_subs_of_mem_summands hXm
        have hXS := G.sub hd'S hXsub
        have := size_le_of_mem_subs hXsub
        have hXt := (G.lt_OF_psiOmS hX hXS htS).mpr hXd
        exact ih X (by simp only [Tm.size]; omega) (hsub (subs_psi_p (subs_om hXsub)))
          (by rcases hX with ⟨n, a, e⟩ | ⟨n, p, b', e⟩
              · exact Or.inl ⟨n, a, e⟩
              · exact Or.inr ⟨_, b', e⟩) hXt
      · have hm := (G.nf _ hκS).xi.1
        have hlm : lev (Tm.Om d) = m := by simp only [lev] at hl ⊢; omega
        refine (baseOf_xi_iff m δ _).mpr ⟨kTerm_lt_psi hm hlm, ?_⟩
        refine inC_mono_node δ δ _ δ _ ((baseOf_xi_iff m δ _).mp hbt).2 (fun u hu hun hut => ?_)
          (fun _ _ _ h => h)
        have := size_le_of_mem_subs hu
        exact ih u (by simp only [Tm.size]; omega) (hsub (subs_psi_p (subs_xi hu))) hun hut
    · have hβ := lt_psi_psi_same.mp hvt
      have hβsub : β ∈ subs (predT c) := hsub (mem_subs_psi_a _ β)
      have hβF := hbF.of_mem_subs hβsub
      have hβs : β.size < (predT c).size := by
        have := size_le_of_mem_subs hv; simp only [Tm.size] at this; omega
      exact lt_psi_psi_same.mpr (lt_pred_of_lt_succ hcF hc hβF hβ (ne_of_mem_subs_lt hβs))
    · have hne : κ ≠ .Om d := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT (κ := κ) (β := β) (π := .Om d) (γ := predT c) hl hne hπκ).mpr
        ((lt_psi_psi_gtT (κ := κ) (β := β) (π := .Om d) (γ := c) hl hne hπκ).mp hvt)

/-- `Ψ_{Ω_d}(b+1)` が標準形なら `Ψ_{Ω_d}(b)` も標準形 -/
theorem psi_pred_WNF : WNF (.Psi (.Om d) (predT c)) := by
  have hcF := h.psi.aF
  have hbF := predT_WNF hcF hc
  have hP := h.psi
  refine WNF.mk_psi ⟨hP.tgt, hP.piF, hbF, (fun _ _ e => by cases e), ?_⟩
  -- `b ∈ C(b+1, Ψ(b+1))` から `b ∈ C(b, Ψ(b))`
  obtain ⟨ys, hys⟩ := summands_of_isSucc hc
  have hbC : inC (predT c) c (.Psi (.Om d) c) = true := by
    refine (inC_iff_summands _ _ _).mpr (fun s hs => ?_)
    rw [summands_predT hcF hys] at hs
    exact (inC_iff_summands _ _ _).mp hP.Ca s (by rw [hys]; exact List.mem_append_left _ hs)
  refine inC_mono_node _ _ _ _ _ hbC (fun v hv hvn hvt => node_lt_psi_pred h hc v hv hvn hvt)
    (fun v hv hvs hvc => lt_pred_of_lt_succ hcF hc (hbF.of_mem_subs hv) hvc
      (ne_of_mem_subs_lt hvs))

/-- `Ψ_{Ω_d}(b+1)` 未満の主要項は `Ψ_{Ω_d}(b)` 以下 -/
theorem prin_le_psi_pred {x : Tm} (hxF : WNF x) (hxp : isPrincipal x = true)
    (hx : Lt x (.Psi (.Om d) c)) : Le x (.Psi (.Om d) (predT c)) := by
  have hcF := h.psi.aF
  have hψF := psi_pred_WNF h hc
  have hlx : lev x ≤ lev (Tm.Om d) := (lev_le_of_lt_gen hx : lev x ≤ lev (Tm.Psi (.Om d) c))
  rcases Nat.lt_or_eq_of_le hlx with hl | hl
  · exact Or.inr (lt_of_lev_lt' hl)
  by_cases hb : isBot x = true
  · exact Or.inr (bot_ltY hb (by rw [hl]; exact Nat.le_refl _) rfl rfl hψF)
  rcases shape_prinOF hxF hxp (Bool.eq_false_iff.mpr hb) with ⟨e, rfl⟩ | hX | ⟨d', β, rfl⟩
  · exact Or.inr (lt_om_psiOmG.mpr (lt_om_psiOmG.mp hx))
  · exact Or.inr ((lt_OF_psiOmY hX hxF hψF).mpr ((lt_OF_psiOmY hX hxF h).mp hx))
  · have hl' : lev (Tm.Om d') = lev (Tm.Om d) := hl
    have hd'F := hxF.psi.piF.om.1
    have hdF := h.psi.piF.om.1
    rcases triY hd'F hdF with hd'd | rfl | hdd'
    · have hO : Lt (Tm.Om d') (.Om d) := lt_om_iffG.mpr hd'd
      have hne : Tm.Om d' ≠ .Om d := fun e => Lt.ne hO e
      have hnlt := Lt.asymmY hxF.psi.piF h.psi.piF hO
      exact Or.inr ((lt_psi_psi_ltT hl' hne hnlt).mpr
        (baseOf_om_psiOmY hxF hψF (ne_gt_of_le (Or.inr hd'd))))
    · rcases le_pred_of_lt_succ hcF hc hxF.psi.aF (lt_psi_psi_same.mp hx) with e | h'
      · exact Or.inl (by rw [e])
      · exact Or.inr (lt_psi_psi_same.mpr h')
    · have hO : Lt (Tm.Om d) (.Om d') := lt_om_iffG.mpr hdd'
      have hne : Tm.Om d' ≠ .Om d := fun e => Lt.ne hO e.symm
      exact Or.inr ((lt_psi_psi_gtT hl' hne hO).mpr ((lt_psi_psi_gtT hl' hne hO).mp hx))

end

theorem summands_fsTermY (pi b : Tm) (n : Nat) :
    summands (fsTermY pi b n) = List.replicate (n + 1) (.Psi pi b) := by
  unfold fsTermY
  exact summands_ofSummands _ (fun s hs => by rw [List.eq_of_mem_replicate hs]; rfl)

theorem fsTermY_WNF {pi b : Tm} (hψ : WNF (.Psi pi b)) : ∀ n, WNF (fsTermY pi b n)
  | 0 => hψ
  | n + 1 => by
    show WNF (ofSummands (Tm.Psi pi b :: List.replicate (n + 1) (Tm.Psi pi b)))
    have e : ofSummands (Tm.Psi pi b :: List.replicate (n + 1) (Tm.Psi pi b)) =
        .plus (.Psi pi b) (fsTermY pi b n) := by
      cases n <;> rfl
    rw [e]
    refine WNF.mk_plus hψ (fsTermY_WNF hψ n) rfl ?_ ?_
    · intro e'
      have := congrArg summands e'
      rw [summands_fsTermY] at this
      simp [summands] at this
    · intro h' rest hs
      rw [summands_fsTermY, List.replicate_succ, List.cons.injEq] at hs
      rw [← hs.1, cmp_self]
      decide

/-- 基本列の性質（大基数の仮定なし）：`Ψ_π(b+1)` が標準形で `π = Ω_0` か `Ω_{c'+1}` なら、`Ψ_π(b)·(n+1)` は
    標準形で狭義増加し、`Ψ_π(b+1)` 未満で、`Ψ_π(b+1)` 未満の標準形はどれかの `Ψ_π(b)·(n+1)` 未満 -/
theorem fs_psi_succY {pi c : Tm} (h : WNF (.Psi pi c))
    (hpi : pi = .Om .zero ∨ ∃ c', pi = .Om c' ∧ isSucc c' = true) (hc : isSucc c = true) :
    WNF (.Psi pi (predT c)) ∧ (∀ n, WNF (fsTermY pi (predT c) n)) ∧
      (∀ n, Lt (fsTermY pi (predT c) n) (fsTermY pi (predT c) (n + 1))) ∧
      (∀ n, Lt (fsTermY pi (predT c) n) (.Psi pi c)) ∧
      (∀ x, WNF x → Lt x (.Psi pi c) → ∃ n, Lt x (fsTermY pi (predT c) n)) := by
  obtain ⟨d, rfl⟩ : ∃ d, pi = .Om d := by
    rcases hpi with e | ⟨c', e, -⟩
    · exact ⟨_, e⟩
    · exact ⟨_, e⟩
  have hcF := h.psi.aF
  have hψF := psi_pred_WNF h hc
  have hψt : Lt (.Psi (.Om d) (predT c)) (.Psi (.Om d) c) := lt_psi_psi_same.mpr (lt_predT hcF hc)
  refine ⟨hψF, fsTermY_WNF hψF, fun n => ?_, fun n => ?_, ?_⟩
  · unfold Lt
    rw [cmp_eq, summands_fsTermY, summands_fsTermY, List.replicate_succ' (n := n + 1)]
    exact cmpList_append_lt _ _ (by simp)
  · exact lt_of_head_lt rfl (by rw [summands_fsTermY, List.replicate_succ])
      ((lt_principal_iff rfl rfl).mp hψt)
  · -- 長さ `k` の和は `Ψ_π(b)·(k+1)` 未満
    have key : ∀ x, WNF x → Lt x (.Psi (.Om d) c) →
        cmpList (summands x) (List.replicate ((summands x).length + 1) (.Psi (.Om d) (predT c)))
          = .lt := by
      intro x
      induction x using size_induction with
      | h x ih =>
      intro hxF hx
      cases hxp : isPrincipal x
      · cases x with
        | zero => exact cmpList_nil_cons _ _
        | plus a r =>
          obtain ⟨haF, hrF, hap, -⟩ := hxF.plus
          have hat : Lt a (.Psi (.Om d) c) := (lt_plus_prin_iffY hxF rfl).mp hx
          have hrt : Lt r (.Psi (.Om d) c) := lt_transY hrF hxF h (lt_plus_rightY hxF) hx
          have ihr := ih r (by simp only [Tm.size]; omega) hrF hrt
          rw [summands_plus, List.length_cons, List.replicate_succ]
          rcases prin_le_psi_pred h hc haF hap hat with e | h'
          · rw [e, cmpList_cons_cons_eq _ _ (cmpP_self _)]
            exact ihr
          · have e : cmpP a (.Psi (.Om d) (predT c)) = .lt := (lt_principal_iff hap rfl).mp h'
            rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
        | _ => simp [isPrincipal] at hxp
      · rw [summands_principal hxp]
        simp only [List.length_cons, List.length_nil, List.replicate_succ, List.replicate_zero]
        rcases prin_le_psi_pred h hc hxF hxp hx with e | h'
        · rw [e, cmpList_cons_cons_eq _ _ (cmpP_self _)]
          exact cmpList_nil_cons _ _
        · have e : cmpP x (.Psi (.Om d) (predT c)) = .lt := (lt_principal_iff hxp rfl).mp h'
          rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    intro x hxF hx
    refine ⟨(summands x).length, ?_⟩
    unfold Lt
    rw [cmp_eq, summands_fsTermY]
    exact key x hxF hx

/-- 到達不能基数 `π = Ξ_n(d)` への崩壊では `·ω` の基本列は作れない：`b < c` なら
    `Ψ_π(b)·(k+1) < Ω_{Ψ_π(b)+1} < Ψ_π(c)`（設計の「到達不能基数への Ψ は Ω の入れ子」） -/
theorem psi_xi_gapY {n : Nat} {d b c : Tm} (hb : WNF (.Psi (.Xi n d) b))
    (hc : WNF (.Psi (.Xi n d) c)) (hbc : Lt b c) :
    WNF (.Om (succT (.Psi (.Xi n d) b))) ∧
      (∀ k, Lt (fsTermY (.Xi n d) b k) (.Om (succT (.Psi (.Xi n d) b)))) ∧
      Lt (.Om (succT (.Psi (.Xi n d) b))) (.Psi (.Xi n d) c) := by
  refine ⟨WNF.om_succT hb, fun k => ?_, ?_⟩
  · exact lt_of_head_lt rfl (by rw [summands_fsTermY, List.replicate_succ])
      ((lt_principal_iff rfl rfl).mp (lt_succT_om hb))
  · rw [lt_om_OFG (Or.inr ⟨n, d, c, rfl⟩) hc]
    have e1 : cmpP (.Psi (.Xi n d) b) (.Psi (.Xi n d) c) = .lt :=
      (lt_principal_iff rfl rfl).mp (lt_psi_psi_same.mpr hbc)
    unfold Lt
    rw [cmp_eq, summands_succT]
    show cmpList ([.Psi (.Xi n d) b] ++ [one]) [.Psi (.Xi n d) c] = .lt
    rw [List.singleton_append, cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]

end MahloOCF
