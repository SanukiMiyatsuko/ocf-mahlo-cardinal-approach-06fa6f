import Mahlo.FS.Props
import Mahlo.WF.Fund

/-! `Ξ_n(d)` の列の始点 `Ψ_{Ξ_n(d)}(d+1)` は標準形（`wnf_base_xi`）。

標準形の条件 `d+1 ∈ C(d+1, Ψ_{Ξ_n(d)}(d+1))` は、`d ∈ C(d, Ξ_n(d))`（`xi_selfY`）から、`d` の部分項で
`Ξ_n(d)` 未満のものが `Ψ_{Ξ_n(d)}(d+1)` 未満であること（`sub_lt_base_xi`）で移す。後者は部分項の大きさの
帰納法で、比較の規則（`Ψ_{Ξ_n(d)}(d+1)` の標準形を使わない形）だけで示す。 -/

namespace MahloOCF.FS

open Tm

/-- `Ω` の不動点 `X` と `Ω_e`（`X` の標準形を使わない形）：`Ω_e < X` ⟺ `e < X` -/
theorem lt_om_OF' {e X : Tm} (hX : IsOF X) (hX1 : 1 ≤ lev X) : Lt (.Om e) X ↔ Lt e X := by
  rcases Nat.lt_trichotomy (max 1 (lev e)) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' (by omega), fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

section
variable {n : Nat} {d : Tm} (h : WNF (.Xi n d))
include h

/-- `d` の部分項で `Ξ_n(d)` 未満のものは `Ψ_{Ξ_n(d)}(d+1)` 未満 -/
theorem sub_lt_base_xi : ∀ u, u ∈ subs d → WNF u → Lt u (.Xi n d) →
    Lt u (.Psi (.Xi n d) (succT d)) := by
  have hn := h.xi.1
  have hDOF : IsOF (.Psi (.Xi n d) (succT d)) := Or.inr ⟨n, d, succT d, rfl⟩
  have hπOF : IsOF (.Xi n d) := Or.inl ⟨n, d, rfl⟩
  have hD1 : 1 ≤ lev (Tm.Psi (.Xi n d) (succT d)) := by simp only [lev]; exact hn
  have hDp : isPrincipal (Tm.Psi (.Xi n d) (succT d)) = true := rfl
  intro u
  induction u using size_induction with
  | h u ih =>
  intro hu huF hlt
  have hlev : lev u ≤ n := lev_le_of_lt_gen hlt
  have hsz : u.size ≤ d.size := size_le_of_mem_subs hu
  -- `Ξ_n(f)`（`d` の部分項、`Ξ_n(d)` 未満）は `Ψ_{Ξ_n(d)}(d+1)` の底の条件を満たす
  have xiBase : ∀ f, Tm.Xi n f ∈ subs d → WNF (.Xi n f) → Lt (.Xi n f) (.Xi n d) →
      (Tm.Xi n f).size ≤ u.size →
      baseOf (.Xi n f) (.Psi (.Xi n d) (succT d)) = true := by
    intro f hfs hfF hfπ hfsz
    refine (baseOf_xi_iff n f _).mpr ⟨kTerm_lt_psi hn rfl, ?_⟩
    refine inC_mono_node f f (.Xi n f) f _ (xi_selfY hfF) (fun v hv _ hvlt => ?_) (fun _ _ _ h => h)
    have hvF := hfF.of_mem_subs (subs_xi hv)
    have hvs := size_le_of_mem_subs hv
    exact ih v (by simp only [Tm.size] at hfsz; omega) (subs_trans hfs (subs_xi hv)) hvF
      (lt_transY hvF hfF h hvlt hfπ)
  rcases Nat.lt_or_eq_of_le hlev with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  cases u with
  | zero => simp only [lev] at hl; omega
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := huF.plus
    have hasub : a ∈ subs d := subs_trans hu (subs_plus_l (self_mem_subs a))
    have haπ := lt_transY ha huF h (lt_plus_leftY huF) hlt
    exact (lt_plus_prin_iffY huF hDp).mpr (ih a (by simp only [Tm.size]; omega) hasub ha haπ)
  | M k => exact M_lt_psi (by simp only [lev] at hl ⊢; omega)
  | Om e =>
    have heF := huF.om.1
    have heπ : Lt e (.Xi n d) := (lt_om_OFG hπOF h).mp hlt
    have hesub : e ∈ subs d := subs_trans hu (subs_om (self_mem_subs e))
    exact (lt_om_OF' hDOF hD1).mpr (ih e (by simp only [Tm.size]; omega) hesub heF heπ)
  | Xi m f =>
    simp only [lev] at hl
    subst hl
    have hgt : cmp (.Xi m d) (.Xi m f) = .gt := by
      rw [swapY huF h]
      have : cmp (.Xi m f) (.Xi m d) = .lt := hlt
      rw [this]; rfl
    exact (lt_xi_psi_iff (π := .Xi m d) (γ := succT d) (f := f) (n := m) rfl).mpr
      ⟨hgt, xiBase f hu huF hlt (Nat.le_refl _)⟩
  | Psi κ β =>
    have hP := huF.psi
    have hκsub : κ ∈ subs d := subs_trans hu (subs_psi_p (self_mem_subs κ))
    have hκF := hP.piF
    have hlκ : lev κ = lev (Tm.Xi n d) := by simp only [lev] at hl ⊢; exact hl
    have hκs : κ.size < (Tm.Psi κ β).size := by simp only [Tm.size]; omega
    rcases triY hκF h with hκπ | rfl | hπκ
    · have hne : κ ≠ .Xi n d := fun e => Lt.ne hκπ e
      have hnlt := Lt.asymmY hκF h hκπ
      refine (lt_psi_psi_ltT hlκ hne hnlt).mpr ?_
      rcases hP.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · refine (baseOf_om_succ hs).mpr ?_
        have hcF := hκF.om.1
        have hcπ : Lt c (.Xi n d) := (lt_om_OFG hπOF h).mp hκπ
        have hcsub : c ∈ subs d := subs_trans hκsub (subs_om (self_mem_subs c))
        have hcs : c.size < (Tm.Psi (.Om c) β).size := by simp only [Tm.size]; omega
        -- `c` の加数（`d` の部分項）は `Ψ_{Ξ_n(d)}(d+1)` 未満
        have hsum : ∀ s, s ∈ summands c → Lt s (.Psi (.Xi n d) (succT d)) := by
          intro s hs'
          have hsF := (summands_WNF c hcF s hs').1
          have hss : s ∈ subs c := mem_subs_of_mem_summands hs'
          have hsc : Le s c := by
            obtain ⟨h', rest, e⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hs')
            have hhd := head_leY hcF e
            have hsh : Le s h' := by
              rw [e] at hs'
              rcases List.mem_cons.mp hs' with rfl | hs'
              · exact Or.inl rfl
              · exact le_of_ne_gtY hsF (summands_WNF c hcF h' (by rw [e]; exact List.mem_cons_self)).1
                  (le_head_of_nfl (by rw [← e]; exact nfl_summands hcF) s hs')
            exact le_transY hsF (summands_WNF c hcF h' (by rw [e]; exact List.mem_cons_self)).1 hcF
              hsh hhd
          have hsπ : Lt s (.Xi n d) := lt_of_le_of_ltY hsF hcF h hsc hcπ
          have := size_le_of_mem_subs hss
          exact ih s (by omega) (subs_trans hcsub hss) hsF hsπ
        unfold omOf
        split
        · rename_i hfix
          have hpp : isPrincipal (predT c) = true := fixed_principal hfix
          exact hsum _ (predT_mem_summands hcF hs hpp)
        · refine (lt_om_OF' hDOF hD1).mpr ?_
          obtain ⟨ys, hys⟩ := summands_of_isSucc hs
          cases hy : ys with
          | nil =>
            have e : predT c = .zero := by rw [predT_of_summands hys, hy]; rfl
            rw [e]; exact zero_lt (by intro e; cases e)
          | cons y rest =>
            have hpred : summands (predT c) = y :: rest := by
              rw [summands_predT hcF hys, hy]
            have hyc : y ∈ summands c := by rw [hys, hy]; exact List.mem_cons_self
            have hyD := hsum y hyc
            exact lt_of_head_lt hDp hpred
              ((lt_principal_iff (summands_WNF c hcF y hyc).2 hDp).mp hyD)
      · simp only [lev] at hlκ
        subst hlκ
        exact xiBase δ hκsub hκF hκπ (by simp only [Tm.size]; omega)
    · exfalso
      have := size_le_of_mem_subs hκsub
      simp only [Tm.size] at this hsz
      omega
    · have hne : κ ≠ .Xi n d := fun e => Lt.ne hπκ e.symm
      refine (lt_psi_psi_gtT hlκ hne hπκ).mpr ?_
      exact not_base_of_lt_tgtY huF h (Or.inr (Or.inr ⟨n, d, rfl⟩)) hlκ hπκ hlt

/-- `Ξ_n(d)` の列の始点 `Ψ_{Ξ_n(d)}(d+1)` は標準形 -/
theorem wnf_base_xi : WNF (base (.Xi n d)) := by
  have hdF := h.xi.2.1
  have hsd := succT_WNF hdF
  show WNF (.Psi (.Xi n d) (sc d))
  refine WNF.mk_psi ⟨Or.inr (Or.inr ⟨n, d, rfl⟩), h, hsd, fun _ _ e => by cases e; exact lt_succT d, ?_⟩
  refine inC_succT (inC_one (succT_ne_zero d)) ?_
  refine inC_mono_node d d (.Xi n d) (succT d) _ (xi_selfY h)
    (fun v hv _ hvlt => sub_lt_base_xi h v hv (hdF.of_mem_subs hv) hvlt)
    (fun v hv _ hvd => lt_transY (hdF.of_mem_subs hv) hdF hsd hvd (lt_succT d))

end

end MahloOCF.FS

namespace MahloOCF.FS

open Tm

/-- 崩壊 `Ψ_π(X)` の列の性質（真の部分項の性質を使ってよい） -/
def PsiCase : Prop :=
  ∀ π X, WNF (.Psi π X) → (∀ u, u.size < (Tm.Psi π X).size → WNF u → Props u) → Props (.Psi π X)

/-- `Ξ_n(d)` の始点は示したので、崩壊の場合の仮定は `PsiCase` だけでよい -/
theorem psiProps_of (h : PsiCase) : PsiProps := ⟨h, fun _ _ hx => wnf_base_xi hx⟩

end MahloOCF.FS
