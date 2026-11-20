import Mahlo.FS.BachZ

/-! `Ψ` の持ち上げ（`lbi_psi`）：引数の区間 `(A, A']` の各 `B` で `Ψ_π(A) ≤ Ψ_π(B)[0]` なら、
`LBI (Ψ_π(A)) (Ψ_π(A'))`。区間の他の主要項は、

* 別の崩壊先 `ρ` の `Ψ_ρ(C)`：`ρ < π` で、`Ψ_π(A)` は `Ψ_ρ` の値域の下にあり、`Ψ_ρ(C)[0]` 以下
  （`below_range`：`Ω` への崩壊は 0 番目が `Ω_{c-1}` 以上、`Ξ` への崩壊は前線の元が 0 番目未満（隙間））。
* `Ω_w`（`π = Ξ`）：`w` は区間の中なので帰納法、`Ξ_m(e)`：0 番目は始点 `Ψ_{Ξ_m(e)}(e+1)` で `Ψ_π(A)` より大きい。 -/

namespace MahloOCF.FS

open Tm

/-! ### 0 番目の補題 -/

theorem psiOm_succ_f0 {d X : Tm} (h : WNF (.Psi (.Om d) X)) (hs : isSucc X = true) :
    fund (.Psi (.Om d) X) .zero = mulNat (.Psi (.Om d) (predT X)) 2 := by
  have hcs := cs_succ_om (d := d) h.psi.aF hs
  have hdom : dom (.Psi (.Om d) X) = .omega := by rw [dom_psi, hcs]; rfl
  rw [fund_zero_omega hdom, fundNat_psi, hcs]
  rfl

theorem psiOm_zero_f0 {c : Tm} (hc0 : c ≠ .zero) :
    fund (.Psi (.Om c) .zero) .zero = mulNat (omOf (predT c)) 2 := by
  have hcs : cs (Om c) zero = .mul (omOf (pred c)) 2 := by rw [cs_zero_om, ite_eq_right hc0]
  have hdom : dom (.Psi (.Om c) .zero) = .omega := by rw [dom_psi, hcs]; rfl
  rw [fund_zero_omega hdom, fundNat_psi, hcs]
  rfl

theorem le_mulNat_two {B : Tm} (hB : WNF B) (hBp : isPrincipal B = true) : Le B (mulNat B 2) :=
  Or.inr (lt_plus_leftY (show WNF (.plus B B) from wnf_mulNat hB hBp 2))

/-- 極限の `X` の和の分け方 -/
theorem exists_split {X : Tm} (hX0 : X ≠ .zero) : ∃ pre R, summands X = pre ++ [R] :=
  ⟨_, _, (List.dropLast_concat_getLast (summands_ne_nil hX0)).symm⟩

/-- `Ψ_{Ω_c}(X)`（`c` は後者）の 0 番目は `Ω_{c-1}` 以上 -/
theorem psiOm_f0_ge {c X : Tm} (h : WNF (.Psi (.Om c) X)) (hc : isSucc c = true) :
    Le (omOf (predT c)) (fund (.Psi (.Om c) X) .zero) := by
  have hπ := h.psi.piF
  have hcF := hπ.om.1
  have hpF := predT_WNF hcF hc
  have hoF := wnf_omOf hpF
  have hlt : ∀ A, WNF (.Psi (.Om c) A) → Lt (omOf (predT c)) (.Psi (.Om c) A) := fun A hA =>
    (baseOf_om_succ hc).mp (base_selfY hA)
  by_cases hX0 : X = .zero
  · subst hX0
    have hc0 : c ≠ .zero := by intro e; rw [e] at hc; cases hc
    rw [psiOm_zero_f0 hc0]
    exact le_mulNat_two hoF (omOf_principal _)
  · by_cases hs : isSucc X = true
    · rw [psiOm_succ_f0 h hs]
      have hB := psi_pred_WNF h hs
      exact Or.inr (lt_of_lt_of_leY hoF hB (wnf_mulNat hB rfl 2) (hlt _ hB) (le_mulNat_two hB rfl))
    · obtain ⟨pre, R, hsX⟩ := exists_split hX0
      obtain ⟨c', x, he, -, -, -⟩ := psi_lim_f0 h hsX hs
      have hw := wnf_f0 h
      rw [he] at hw ⊢
      exact Or.inr (hlt _ hw)

/-- 隙間：主要項 `b` の真の部分項で `b` 未満のものは `b[0]` 未満 -/
theorem gap_f0 {b v : Tm} (hb : WNF b) (hbp : isPrincipal b = true) (hd1 : dom b ≠ .one)
    (hv : v ∈ subs b) (hne : v ≠ b) (hlt : Lt v b) : Lt v (fund b .zero) := by
  have hI := inv_of b hb
  cases hd : dom b with
  | zero => rw [(dom_eq_zero_iff hb).mp hd] at hlt; exact absurd hlt (not_lt_zero _)
  | one => exact absurd hd hd1
  | omega => rw [fund_zero_omega hd]; exact (hI.1 hd).gap 0 v hv hne hlt
  | big σ =>
    rw [fund_zero_big hd]
    have hB := hI.2 σ hd
    exact hB.gapP hbp .zero v WNF.zero hB.props.pos hv hne hlt

/-- `Ψ_ρ` の値域の下にある項（`ρ` の底の条件を満たさない）は `Ψ_ρ(C)[0]` 以下 -/
theorem below_range {ρ C x : Tm} (hb : WNF (.Psi ρ C)) (hx : WNF x)
    (hnb : baseOf ρ x = false) (hlev : ∀ n d, ρ = .Xi n d → Lt (kTerm (n - 1)) x) :
    Le x (fund (.Psi ρ C) .zero) := by
  have hP := hb.psi
  rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨n, d, rfl⟩
  · cases x with
    | zero => exact zero_le _
    | _ => rw [(baseOf_om_zero _).mpr (by intro e; cases e)] at hnb; cases hnb
  · have hcF := hP.piF.om.1
    have hoF := wnf_omOf (predT_WNF hcF hc)
    have h1 : ¬ Lt (omOf (predT c)) x := by
      intro h; rw [(baseOf_om_succ hc).mpr h] at hnb; cases hnb
    exact le_transY hx hoF (wnf_f0 hb) (le_of_not_ltY hoF hx h1) (psiOm_f0_ge hb hc)
  · have hk := hlev n d rfl
    have hnC : inC d d x = false := by
      cases e : inC d d x with
      | false => rfl
      | true => rw [(baseOf_xi_iff n d x).mpr ⟨hk, e⟩] at hnb; cases hnb
    have hex : ∃ w, w ∈ fr (.Xi n d) (.Xi n d) ∧ ¬ Lt w x := by
      refine exists_of_not_forall_mem _ (fun hall => ?_)
      have : inC d d x = true :=
        inC_of_fr d (xi_selfY hP.piF) (fun _ _ h => h)
          (fun w hw => inC_of_lt_node (fr_node hw) (hall w (by rw [fr_xi_self]; exact hw)))
      rw [this] at hnC; cases hnC
    obtain ⟨w, hw, hwx⟩ := hex
    obtain ⟨hwF, hwρ, -, -, hwsub⟩ := fr_elem hP.piF hw
    have hxw := le_of_not_ltY hwF hx hwx
    have hwb : Lt w (.Psi (.Xi n d) C) := sub_lt_psi hP.piF hP.tgt C w hwsub (Lt.ne hwρ) hwF hwρ
    have hd1 : dom (.Psi (.Xi n d) C) ≠ .one := by
      rw [dom_psi]; intro e; have := (dom_one_iff_psi.mp e).1; cases this
    have hgap := gap_f0 hb rfl hd1 (subs_psi_p hwsub) (Lt.ne hwb) hwb
    exact Or.inr (lt_of_le_of_ltY hx hwF (wnf_f0 hb) hxw hgap)

/-- 階 `n` の `0` でない主要項（`M` でない）は `M_{n-1}` より大きい -/
theorem kTerm_lt_of_lev {x : Tm} {n : Nat} (hx : WNF x) (hxp : isPrincipal x = true)
    (hxM : ∀ k, x ≠ .M k) (hl : lev x = n) : Lt (kTerm (n - 1)) x := by
  have hx0 : x ≠ .zero := by intro e; rw [e] at hxp; cases hxp
  unfold kTerm
  split
  · exact zero_lt hx0
  · rename_i hn
    have hkF : WNF (.M (n - 1)) := WNF.M' (by omega)
    rcases triY hkF hx with h | e | h
    · exact h
    · exact absurd e.symm (hxM _)
    · have := (lt_M_iffY hx (by omega)).mp h
      omega

theorem f0_om_reg {w : Tm} (h : omReg w) : fund (.Om w) .zero = .Psi (.Om w) .zero := by
  rw [fund_zero_big (dom_om_reg h), fundBig_om_reg h, oadd_zero]
  rfl

theorem f0_om_lim {w : Tm} (hw : WNF (.Om w)) (h : ¬ omReg w) :
    fund (.Om w) .zero = .Om (sc (fund w .zero)) := by
  have hd := dom_om_lim h
  cases e : dom w with
  | zero => exact absurd (Or.inl ((dom_eq_zero_iff hw.om.1).mp e)) h
  | one => exact absurd (Or.inr ((dom_eq_one_iff hw.om.1).mp e)) h
  | omega => rw [fund_zero_omega (by rw [hd, e]), fundNat_om h, fund_zero_omega e]
  | big σ => rw [fund_zero_big (σ := σ) (by rw [hd, e]), fundBig_om_lim h, fund_zero_big e]

/-! ### `Ψ` の持ち上げ -/

/-- `Ψ` の持ち上げ：引数の区間 `(A, A']` の `B` で `Ψ_π(A) ≤ Ψ_π(B)[0]` なら `LBI (Ψ_π(A)) (Ψ_π(A'))` -/
theorem lbi_psi {π A A' : Tm} (hA : WNF (.Psi π A)) (hA' : WNF (.Psi π A'))
    (harg : ∀ B, WNF (.Psi π B) → Lt A B → Le B A' → Le (.Psi π A) (fund (.Psi π B) .zero)) :
    LBI (.Psi π A) (.Psi π A') := by
  have hP := hA.psi
  have hπ := hP.piF
  have hlv : ∀ b, Lt (.Psi π A) b → Le b (.Psi π A') → lev b = lev π := by
    intro b h1 h2
    have e1 : lev (Tm.Psi π A) ≤ lev b := lev_le_of_lt_gen h1
    have e2 : lev b ≤ lev (Tm.Psi π A') := by
      rcases h2 with rfl | h2
      · exact Nat.le_refl _
      · exact lev_le_of_lt_gen h2
    simp only [lev] at e1 e2
    omega
  intro b
  induction b using size_induction with
  | h b ih =>
  intro hb hxb hby
  have hl := hlv b hxb hby
  cases b with
  | zero => exact absurd hxb (not_lt_zero _)
  | plus h' r => exact le_f0_of_lt_plus hA (Or.inr rfl) hb hxb
  | M n =>
    exfalso
    have hn := hb.M
    have := (lt_M_iffY hA hn).mp hxb
    simp only [lev] at hl this
    omega
  | Om w =>
    have hwF := hb.om.1
    rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨m, d, rfl⟩
    · exfalso
      rcases hby with e | h
      · cases e
      · exact not_lt_zero w (lt_om_psiOmG.mp h)
    · exfalso
      have hcF := hπ.om.1
      have hpF := predT_WNF hcF hc
      have hwc : Lt w c := by
        rcases hby with e | h
        · cases e
        · exact lt_om_psiOmG.mp h
      have hwp : Le w (predT c) := le_of_lt_succT hwF hpF (by rw [succT_predT hcF hc]; exact hwc)
      have h1 := om_le_omOf hb hpF hwp
      have h2 : Lt (omOf (predT c)) (.Psi (.Om c) A) := (baseOf_om_succ hc).mp (base_selfY hA)
      exact Lt.irrefl _ (lt_transY hA hb hA hxb (lt_of_le_of_ltY hb (wnf_omOf hpF) hA h1 h2))
    · have hOF : ∀ Y, IsOF (Tm.Psi (.Xi m d) Y) := fun Y => Or.inr ⟨m, d, Y, rfl⟩
      have hwA : Lt (.Psi (.Xi m d) A) w := by
        rcases triY hA hwF with h | e | h
        · exact h
        · exfalso; have := hb.om.2; rw [← e] at this; cases this
        · exact absurd hxb (Lt.asymmY hb hA ((lt_om_OFG (hOF A) hA).mpr h))
      have hwA' : Lt w (.Psi (.Xi m d) A') := by
        rcases hby with e | h
        · cases e
        · exact (lt_om_OFG (hOF A') hA').mp h
      by_cases hr : omReg w
      · rw [f0_om_reg hr]
        rcases hr with h0 | hs
        · rw [h0] at hwA; exact absurd hwA (not_lt_zero _)
        · have hpF := predT_WNF hwF hs
          have hbase : WNF (.Psi (.Om w) .zero) := wnf_base hb (isRegY_of_omReg (Or.inr hs))
          have h1 : Le (.Psi (.Xi m d) A) (predT w) :=
            le_of_lt_succT hA hpF (by rw [succT_predT hwF hs]; exact hwA)
          have h2 := le_omOf hpF
          have h3 : Lt (omOf (predT w)) (.Psi (.Om w) .zero) := (baseOf_om_succ hs).mp (base_selfY hbase)
          exact Or.inr (lt_of_le_of_ltY hA (wnf_omOf hpF) hbase
            (le_transY hA hpF (wnf_omOf hpF) h1 h2) h3)
      · rw [f0_om_lim hb hr]
        have hw0 := ih w (by simp only [Tm.size]; omega) hwF hwA (Or.inr hwA')
        have hw0F := wnf_f0 hwF
        exact Or.inr (lt_of_le_of_ltY hA hw0F (WNF.om_succT hw0F) hw0 (lt_succT_om hw0F))
  | Xi n e =>
    rcases hP.tgt with rfl | ⟨c, rfl, hc⟩ | ⟨m, d, rfl⟩
    · exfalso
      have hOF : IsOF (Tm.Xi n e) := Or.inl ⟨n, e, rfl⟩
      have h1 : Lt (.Om .zero) (.Xi n e) := (lt_om_OFG hOF hb).mpr (zero_lt (by intro h; cases h))
      have h2 : Lt (.Psi (.Om .zero) A') (.Om .zero) := lt_psiOm_om_self _ _
      rcases hby with e' | h
      · cases e'
      · exact Lt.irrefl _ (lt_transY hb hA' hb h (lt_transY hA' WNF.om_zero hb h2 h1))
    · exfalso
      have hOF : IsOF (Tm.Xi n e) := Or.inl ⟨n, e, rfl⟩
      have hcF := hπ.om.1
      have hpF := predT_WNF hcF hc
      have h2 : Lt (omOf (predT c)) (.Psi (.Om c) A) := (baseOf_om_succ hc).mp (base_selfY hA)
      have h3 : Lt (predT c) (.Xi n e) :=
        lt_of_le_of_ltY hpF (wnf_omOf hpF) hb (le_omOf hpF) (lt_transY (wnf_omOf hpF) hA hb h2 hxb)
      have h4 : Lt c (.Xi n e) := by rw [← succT_predT hcF hc]; exact succT_lt_OF hOF hpF hb h3
      have h5 : Lt (.Om c) (.Xi n e) := (lt_om_OFG hOF hb).mpr h4
      have h6 : Lt (.Psi (.Om c) A') (.Om c) := lt_psiOm_om_self _ _
      rcases hby with e' | h
      · cases e'
      · exact Lt.irrefl _ (lt_transY hb hA' hb h (lt_transY hA' hπ hb h6 h5))
    · -- `π = Ξ_m(d)`：0 番目は `Ξ_n(e)` の始点
      have hσT : IsTgt (Tm.Xi n e) := Or.inr (Or.inr ⟨n, e, rfl⟩)
      have hbπ : Lt (.Xi n e) (.Xi m d) := by
        rcases hby with e' | h
        · cases e'
        · exact lt_transY hb hA' hπ h (lt_psi_targetY hA')
      have hlv' : lev (Tm.Xi m d) = lev (Tm.Xi n e) := by simp only [lev] at hl ⊢; omega
      have hnb := not_base_of_lt_tgtY hA hb hσT hlv' hbπ hxb
      rw [fund_zero_big (dom_xi n e), fundBig_xi, oadd_zero]
      refine Or.inr ((lt_psi_psiY hlv').mpr (Or.inr (Or.inl ⟨?_, hbπ, hnb⟩)))
      intro h; rw [h] at hbπ; exact Lt.irrefl _ hbπ
  | Psi ρ C =>
    by_cases hρ : ρ = π
    · subst hρ
      have h1 : Lt A C := lt_psi_psi_same.mp hxb
      have h2 : Le C A' := by
        rcases hby with e | h
        · cases e; exact Or.inl rfl
        · exact Or.inr (lt_psi_psi_same.mp h)
      exact harg C hb h1 h2
    · have hρF := hb.psi.piF
      have hlρ : lev π = lev ρ := by simp only [lev] at hl; omega
      have hby' : Lt (.Psi ρ C) (.Psi π A') := by
        rcases hby with e | h
        · cases e; exact absurd rfl hρ
        · exact h
      rcases (lt_psi_psiY hlρ).mp hxb with ⟨e, -⟩ | ⟨-, hρπ, hnb⟩ | ⟨-, hnρ, hbt⟩
      · exact absurd e.symm hρ
      · -- `ρ < π`：`Ψ_π(A)` は `Ψ_ρ` の値域の下
        refine below_range hb hA hnb (fun n e h => ?_)
        subst h
        exact kTerm_lt_of_lev hA rfl (fun k h => by cases h) (by simp only [lev] at hl ⊢; omega)
      · exfalso
        have hπρ : Lt π ρ := by
          rcases triY hπ hρF with h | h | h
          · exact h
          · exact absurd h.symm hρ
          · exact absurd h hnρ
        rcases (lt_psi_psiY hlρ.symm).mp hby' with ⟨e, -⟩ | ⟨-, -, hbf⟩ | ⟨-, hn, -⟩
        · exact hρ e
        · rw [hbt] at hbf; cases hbf
        · exact hn hπρ

end MahloOCF.FS
