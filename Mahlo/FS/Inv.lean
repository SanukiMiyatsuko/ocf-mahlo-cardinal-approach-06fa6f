import Mahlo.FS.Clo

/-! 基本列の不変量と、構造的な場合（和・正則項・`Ω_c`（`c` 極限））。

FS の公理に要る性質（`NatProps`・`BigProps`：標準形・減少・単調・共終）に加えて、崩壊 `Ψ_π(X)` の列を
部分項の列から組み立てるのに要る性質を持たせる。

* 上界 `ub`：`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)`。`d` は切断（標準形か、崩壊の候補 `Ψ_π(A)`）でよい。
  近似 `Ψ_π(A_n)` が標準形であること（`A_n ∈ C(A_n, Ψ_π(A_n))`）は、`d = Ψ_π(A_n)` に使って示す。
* 隙間 `gap`：`t` の真の部分項で `t` 未満のものは `t[n]` 未満。近似の引数 `A_n` について「`X` の部分項 `Y` が
  `Y < X` なら `Y < A_n`」を出すのに使う。
* 共終数が正則項 `σ` の列では、さらに `σ` が `t` の成分であること（`σC`）、添字が列の項の成分であること（`lo`）、
  `ξ ≤ t[ξ]`（`ge`）。和 `a + M_1` の `[0] = a` のため、隙間は等号つき（`gap`）で、主要項なら狭義（`gapP`）。 -/

namespace MahloOCF.FS

open Tm

/-- `b`（`0` か主要項）が `ξ` 以下で `ξ ∈ C(g, d)` なら `b ⊕ ξ ∈ C(g, d)` -/
theorem inC_oadd_le {b ξ g d : Tm} (hb : WNF b) (hbp : b = .zero ∨ isPrincipal b = true)
    (hξ : WNF ξ) (hbξ : Le b ξ) (hξC : inC ξ g d = true) : inC (oadd b ξ) g d = true := by
  rcases hbp with rfl | hbp
  · exact inC_oadd hb hξ (inC_zero _ _) hξC
  by_cases hbs : b ∈ summands ξ
  · exact inC_oadd hb hξ (inC_of_mem_summands hξ hξC hbs) hξC
  have hξ0 : ξ ≠ .zero := by
    intro e
    subst e
    rcases hbξ with e | h
    · rw [e] at hbp; simp [isPrincipal] at hbp
    · exact not_lt_zero _ h
  obtain ⟨h, r, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hξ0)
  have hhF := summands_WNF ξ hξ h (by rw [hs]; exact List.mem_cons_self)
  have htw : ([b] : List Tm).takeWhile (fun s => leB h s) = [] := by
    cases e : leB h b with
    | false => simp [List.takeWhile, e]
    | true =>
      exfalso
      have h1 : Le h b := le_of_ne_gtY hhF.1 hb (leB_iff.mp e)
      rcases h1 with e' | h1
      · exact hbs (by rw [hs, ← e']; exact List.mem_cons_self)
      · exact not_lt_of_leY hb hξ hbξ (lt_of_head_lt hbp hs ((lt_principal_iff hhF.2 hbp).mp h1))
  rw [oadd_eq_ofSummands hb hξ hs, summands_principal hbp, htw, List.nil_append,
    ofSummands_summands ξ hξ]
  exact hξC

/-- 正則項の始点は `0` か主要項 -/
theorem base_zero_or_prin {σ : Tm} (h : IsRegY σ) : base σ = .zero ∨ isPrincipal (base σ) = true := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · show kTerm (n - 1) = .zero ∨ isPrincipal (kTerm (n - 1)) = true
    unfold kTerm
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

/-! ### 不変量 -/

/-- 共終数 `ω` の列の不変量 -/
structure NatInv (t : Tm) : Prop where
  props : NatProps t
  pos : ∀ n, fundNat t n ≠ .zero
  /-- 上界：`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)` -/
  ub : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC t g d = true → inC (fundNat t n) g d = true
  /-- 隙間：`t` の真の部分項で `t` 未満のものは `t[n]` 未満 -/
  gap : ∀ n v, v ∈ subs t → v ≠ t → Lt v t → Lt v (fundNat t n)
  /-- 2 点の上界：`t[n+1] ∈ C(g, d)` なら `t[n] ∈ C(g, d)` -/
  ub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d → inC (fundNat t (n + 1)) g d = true →
    inC (fundNat t n) g d = true

/-- 共終数が正則項 `σ` の列の不変量 -/
structure BigInv (t σ : Tm) : Prop where
  props : BigProps t σ
  σreg : IsRegY σ
  σsub : σ ∈ subs t
  σle : Le σ t
  /-- `t[ξ] = 0` なら `t` に真の部分項はない（`M_1` の始点） -/
  pos : ∀ ξ, WNF ξ → Lt ξ σ → fundBig t ξ = .zero → ∀ v, v ∈ subs t → v = t
  /-- 共終数は `t` の成分 -/
  σC : ∀ g d, Cut d → inC t g d = true → inC σ g d = true
  /-- 上界：`t`・添字 `ξ`・`σ` の列の始点が `C(g, d)` に入れば `t[ξ] ∈ C(g, d)` -/
  ub : ∀ g d ξ, WNF g → g ≠ .zero → Cut d → WNF ξ → Lt ξ σ → inC (base σ) g d = true →
    inC t g d = true → inC ξ g d = true → inC (fundBig t ξ) g d = true
  /-- 添字は列の項の成分 -/
  lo : ∀ g d ξ, Cut d → WNF ξ → Lt ξ σ → inC (fundBig t ξ) g d = true → inC ξ g d = true
  ge : ∀ ξ, WNF ξ → Lt ξ σ → Le ξ (fundBig t ξ)
  /-- 隙間（等号つき） -/
  gap : ∀ ξ v, WNF ξ → Lt ξ σ → v ∈ subs t → v ≠ t → Lt v t → Le v (fundBig t ξ)
  /-- 隙間（主要項なら狭義） -/
  gapP : isPrincipal t = true → ∀ ξ v, WNF ξ → Lt ξ σ → v ∈ subs t → v ≠ t → Lt v t →
    Lt v (fundBig t ξ)
  /-- 添字での共終性：`x < t` で `x` の `σ` 未満の極大部分項が添字 `ξ > 0` 未満なら `x < t[ξ]` -/
  lclo : ∀ x ξ, WNF x → Lt x t → WNF ξ → Lt .zero ξ → Lt ξ σ → (∀ f, f ∈ lfr σ x → Lt f ξ) →
    Lt x (fundBig t ξ)
  /-- 後者でない添字の項は後者でない（`σ = Ω_0` で添字が `0` のときを除く） -/
  nsucc : ∀ ξ, WNF ξ → Lt ξ σ → ¬ isSucc ξ = true → (ξ ≠ .zero ∨ σ ≠ .Om .zero) →
    ¬ isSucc (fundBig t ξ) = true
  /-- 列の項は `σ` の始点以上 -/
  bge : ∀ ξ, WNF ξ → Lt ξ σ → Le (base σ) (fundBig t ξ)
  /-- 共終数が `M_m` で `t > M_m` なら、列の項は `M_m` 以上 -/
  lbK : ∀ m, σ = .M m → Lt (.M m) t → ∀ ξ, WNF ξ → Lt ξ σ → Le (.M m) (fundBig t ξ)
  /-- 共終数が `M_m` で `t > M_m⁺` なら、列の項は `M_m⁺` 以上 -/
  lbS : ∀ m, σ = .M m → Lt (succM m) t → ∀ ξ, WNF ξ → Lt ξ σ → Le (succM m) (fundBig t ξ)
  /-- 2 点の上界：`ξ < η`、`σ` の始点が `C(g, d)` に入るか `ξ` 以下で、`ξ ∈ C(g, d)`、`t[η] ∈ C(g, d)` なら
      `t[ξ] ∈ C(g, d)` -/
  ub2 : ∀ g d ξ η, WNF g → g ≠ .zero → Cut d → WNF ξ → WNF η → Lt ξ η → Lt η σ →
    (inC (base σ) g d = true ∨ Le (base σ) ξ) → inC ξ g d = true → inC (fundBig t η) g d = true →
    inC (fundBig t ξ) g d = true
  /-- `σ` の始点の証人：`t[ξ] ∈ C(g, d)` なら、`σ` より上の `L` 未満で `σ` の始点以上の項が `C(g, d)` に入る -/
  bw : ∀ g d ξ L, Cut d → WNF ξ → Lt ξ σ → WNF L → Lt σ L → inC (fundBig t ξ) g d = true →
    ∃ u, WNF u ∧ inC u g d = true ∧ Le (base σ) u ∧ Lt u L

/-- 列の不変量 -/
def Inv (t : Tm) : Prop := (dom t = .omega → NatInv t) ∧ (∀ σ, dom t = .big σ → BigInv t σ)

theorem Inv.props {t : Tm} (h : Inv t) : Props t :=
  ⟨fun hd => (h.1 hd).props, fun σ hd => (h.2 σ hd).props⟩

/-- 閉じた点での共終性：`x < t` で `x` の前線（`σ` について）が閉じた点 `β` 未満なら `x < t[β]` -/
theorem BigInv.clo {t σ : Tm} (h : BigInv t σ) {x β : Tm} (hx : WNF x) (hxt : Lt x t) (hβ : WNF β)
    (hβσ : Lt β σ) (hCl : Cl σ β) (hfr : ∀ f, f ∈ fr σ x → Lt f β) : Lt x (fundBig t β) :=
  h.lclo x β hx hxt hβ (hCl.pos h.props.pos) hβσ (fun g hg =>
    hCl g (hx.of_mem_subs (lfr_spec hg).1) (lfr_spec hg).2
      (fun f hf => hfr f (fr_of_lfr hx hg hf)))

/-! ### 補題 -/

theorem oadd_ne_zero_left {a y : Tm} (ha : WNF a) (hy : WNF y) (ha0 : a ≠ .zero) :
    oadd a y ≠ .zero := by
  intro e
  have h := le_oadd_leftW ha hy
  rw [e] at h
  rcases h with h | h
  · exact ha0 h
  · exact not_lt_zero _ h

/-- `x ⊕ y ∈ C(g, d)` なら `y ∈ C(g, d)` -/
theorem inC_of_oadd_right {x y g d : Tm} (hx : WNF x) (hy : WNF y) (h : inC (oadd x y) g d = true) :
    inC y g d = true := by
  cases hsy : summands y with
  | nil => rw [eq_zero_of_summands_nil hsy]; exact inC_zero _ _
  | cons h' r =>
    rw [inC_iff_summandsW (wnf_oadd hx hy)] at h
    rw [inC_iff_summandsW hy]
    intro s hs
    apply h
    rw [summands_oadd hsy (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy))]
    exact List.mem_append_right _ hs

/-- `z + 1 ∈ C(g, d)` なら `z ∈ C(g, d)` -/
theorem inC_of_succT {g d : Tm} : ∀ {z : Tm}, inC (succT z) g d = true → inC z g d = true
  | .zero, _ => inC_zero _ _
  | .plus a b, h => by
    have h' : inC (.plus a (succT b)) g d = true := h
    rw [inC_plus, Bool.and_eq_true] at h' ⊢
    exact ⟨h'.1, inC_of_succT h'.2⟩
  | .M _, h | .Om _, h | .Xi _ _, h | .Psi _ _, h => by
    have h' : inC (.plus _ one) g d = true := h
    rw [inC_plus, Bool.and_eq_true] at h'
    exact h'.1

/-- `a + b` 未満の項は `a` 以下か、`a + y`（`y < b`） -/
theorem lt_plus_cases {a b x : Tm} (h : WNF (.plus a b)) (hx : WNF x) (hlt : Lt x (.plus a b)) :
    Le x a ∨ ∃ y, x = .plus a y ∧ WNF y ∧ Lt y b := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  cases hxp : isPrincipal x
  · cases x with
    | zero => exact Or.inl (zero_le a)
    | plus h' r =>
      obtain ⟨hh, hr, hhp, hr0⟩ := hx.plus
      have e1 : cmpList (h' :: summands r) (a :: summands b) = .lt := by
        have := hlt; unfold Lt at this; rw [cmp_eq] at this; exact this
      rcases hc : cmpP h' a with _ | _ | _
      · exact Or.inl (Or.inr (lt_of_head_lt hap (summands_plus h' r) hc))
      · have e : h' = a := eq_of_cmpP_eqY hh ha hhp hap hc
        subst e
        rw [cmpList_cons_cons_eq _ _ hc] at e1
        refine Or.inr ⟨r, rfl, hr, ?_⟩
        unfold Lt; rw [cmp_eq]; exact e1
      · rw [cmpList_cons_cons_ne _ _ (by rw [hc]; decide), hc] at e1
        cases e1
    | _ => simp [isPrincipal] at hxp
  · exact Or.inl ((lt_prin_plus_iffY hx hxp h).mp hlt)

/-- 和の隙間：`b` の隙間（等号つき）から -/
theorem gap_plus {a b y : Tm} (h : WNF (.plus a b)) (hy : WNF y)
    (G : ∀ v, v ∈ subs b → v ≠ b → Lt v b → Le v y) :
    ∀ v, v ∈ subs (.plus a b) → v ≠ .plus a b → Lt v (.plus a b) → Le v (oadd a y) := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  intro v hv hne hlt
  have hvF := h.of_mem_subs hv
  rcases lt_plus_cases h hvF hlt with hle | ⟨y', rfl, hy', hy'b⟩
  · exact le_transY hvF ha (wnf_oadd ha hy) hle (le_oadd_leftW ha hy)
  · simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | hva | hvb
    · exact absurd e hne
    · exfalso
      have := size_le_of_mem_subs hva
      simp only [Tm.size] at this
      omega
    · have hy's : y' ∈ subs b := subs_trans hvb (subs_plus_r (self_mem_subs y'))
      have hy'ne : y' ≠ b := ne_of_size_lt (by
        have := size_le_of_mem_subs hvb
        simp only [Tm.size] at this
        omega)
      rw [← oadd_plus hvF]
      exact oadd_le_oadd ha hy' hy (G y' hy's hy'ne hy'b)

/-- 和の隙間（狭義）：`b` の隙間（狭義）と `y ≠ 0` から -/
theorem gap_plus_strict {a b y : Tm} (h : WNF (.plus a b)) (hy : WNF y) (hy0 : y ≠ .zero)
    (G : ∀ v, v ∈ subs b → v ≠ b → Lt v b → Lt v y) :
    ∀ v, v ∈ subs (.plus a b) → v ≠ .plus a b → Lt v (.plus a b) → Lt v (oadd a y) := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  intro v hv hne hlt
  have hvF := h.of_mem_subs hv
  rcases lt_plus_cases h hvF hlt with hle | ⟨y', rfl, hy', hy'b⟩
  · exact lt_of_le_of_ltY hvF ha (wnf_oadd ha hy) hle (lt_oadd_left ha hy hy0)
  · simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | hva | hvb
    · exact absurd e hne
    · exfalso
      have := size_le_of_mem_subs hva
      simp only [Tm.size] at this
      omega
    · have hy's : y' ∈ subs b := subs_trans hvb (subs_plus_r (self_mem_subs y'))
      have hy'ne : y' ≠ b := ne_of_size_lt (by
        have := size_le_of_mem_subs hvb
        simp only [Tm.size] at this
        omega)
      rw [← oadd_plus hvF]
      exact oadd_lt_oadd ha hy' hy (G y' hy's hy'ne hy'b)

/-- `y ≠ 0` なら `x ⊕ y` が後者かは `y` で決まる -/
theorem isSucc_oadd {x y : Tm} (hx : WNF x) (hy : WNF y) (hy0 : y ≠ .zero) :
    isSucc (oadd x y) = isSucc y := by
  obtain ⟨h, r, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hy0)
  unfold isSucc
  rw [summands_oadd hs (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy)), hs]
  simp only [List.getLast?_append]
  cases e : (h :: r).getLast? with
  | none => simp at e
  | some v => rfl

/-- 部分項が自身だけの標準形は `0` か `M_n` -/
theorem eq_M_of_subs_self {b : Tm} (hb0 : b ≠ .zero) (h : ∀ v, v ∈ subs b → v = b) :
    ∃ n, b = .M n := by
  cases b with
  | zero => exact absurd rfl hb0
  | M n => exact ⟨n, rfl⟩
  | plus x y =>
    have := congrArg Tm.size (h x (subs_plus_l (self_mem_subs x)))
    simp only [Tm.size] at this; exfalso; omega
  | Om e =>
    have := congrArg Tm.size (h e (subs_om (self_mem_subs e)))
    simp only [Tm.size] at this; exfalso; omega
  | Xi m e =>
    have := congrArg Tm.size (h e (subs_xi (self_mem_subs e)))
    simp only [Tm.size] at this; exfalso; omega
  | Psi p e =>
    have := congrArg Tm.size (h e (subs_psi_a (self_mem_subs e)))
    simp only [Tm.size] at this; exfalso; omega

/-- `M_m < M_m⁺` -/
theorem M_lt_succM {m : Nat} (hm : 1 ≤ m) : Lt (.M m) (succM m) :=
  bot_ltY rfl (show m + 1 ≤ max 1 (m + 1) from Nat.le_max_right 1 (m + 1)) rfl rfl (WNF.succM hm)

/-- `M_m⁺` の中の崩壊は `1 = Ψ_{Ω_0}(0)` だけ -/
theorem psi_mem_subs_succM {m : Nat} {π Y : Tm} (h : Tm.Psi π Y ∈ subs (succM m)) : π = .Om .zero := by
  simp [succM, subs, one] at h
  exact h.1

/-- 正則項は `Ω_0` 未満でない -/
theorem not_lt_om_zero_of_reg {σ : Tm} (hσ : WNF σ) (h : IsRegY σ) : ¬ Lt σ (.Om .zero) := by
  rcases h with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact Lt.irrefl _
  · intro hlt; exact not_lt_zero _ (lt_om_iffG.mp hlt)
  · exact Lt.asymmY WNF.om_zero hσ (lt_of_lev_lt' (by
      simp only [lev, Nat.max_eq_left (Nat.zero_le 1)]; have := hσ.M; omega))
  · have hOF : IsOF (.Xi n p) := Or.inl ⟨n, p, rfl⟩
    exact Lt.asymmY WNF.om_zero hσ ((lt_om_OFG hOF hσ).mpr (zero_lt (by intro e; cases e)))

/-! ### 和 -/

/-- `a + b` が標準形で `0 < y < b` なら `a + y` も標準形 -/
theorem wnf_plus_of_lt {a b y : Tm} (h : WNF (.plus a b)) (hy : WNF y) (hy0 : y ≠ .zero)
    (hyb : Lt y b) : WNF (.plus a y) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  refine WNF.mk_plus ha hy hap hy0 (fun h' rest hs => ?_)
  obtain ⟨h0, r0, hs0⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
  have h1 : cmpP h' h0 ≠ .gt := head_le_of_lt hs hs0 hyb
  have h2 : cmp h0 a ≠ .gt := WNF.plus_head h hs0
  have hh'W := summands_WNF y hy h' (by rw [hs]; exact List.mem_cons_self)
  have hh0W := summands_WNF b hbF h0 (by rw [hs0]; exact List.mem_cons_self)
  have hle1 : Le h' h0 := by
    rcases hc : cmpP h' h0 with _ | _ | _
    · exact Or.inr ((lt_principal_iff hh'W.2 hh0W.2).mpr hc)
    · exact Or.inl (eq_of_cmpP_eqY hh'W.1 hh0W.1 hh'W.2 hh0W.2 hc)
    · exact absurd hc h1
  exact ne_gt_of_le (le_transY hh'W.1 hh0W.1 ha hle1 (le_of_ne_gtY hh0W.1 ha h2))

theorem natInv_plus {a b : Tm} (h : WNF (.plus a b)) (hb : NatInv b) : NatInv (.plus a b) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  have ha0 : a ≠ .zero := by intro e; subst e; cases hap
  refine ⟨natProps_plus h hb.props, fun n => ?_, fun g d n hg hg0 hd hC => ?_, fun n v hv hne hlt => ?_,
    fun g d n hg hg0 hd hC => ?_⟩
  · rw [fundNat_plus]; exact oadd_ne_zero_left ha (hb.props.nf n) ha0
  · rw [inC_plus, Bool.and_eq_true] at hC
    rw [fundNat_plus]
    exact inC_oadd ha (hb.props.nf n) hC.1 (hb.ub g d n hg hg0 hd hC.2)
  · rw [fundNat_plus]
    exact gap_plus_strict h (hb.props.nf n) (hb.pos n) (hb.gap n) v hv hne hlt
  · rw [fundNat_plus] at hC ⊢
    have hp1 := wnf_plus_of_lt h (hb.props.nf (n + 1)) (hb.pos (n + 1)) (hb.props.lt (n + 1))
    rw [oadd_plus hp1, inC_plus, Bool.and_eq_true] at hC
    exact inC_oadd ha (hb.props.nf n) hC.1 (hb.ub2 g d n hg hg0 hd hC.2)

theorem bigInv_plus {a b σ : Tm} (h : WNF (.plus a b)) (hb : BigInv b σ) : BigInv (.plus a b) σ := by
  obtain ⟨ha, hbF, hap, hb0⟩ := h.plus
  have ha0 : a ≠ .zero := by intro e; subst e; cases hap
  have hP := hb.props
  refine {
    props := bigProps_plus h hP
    σreg := hb.σreg
    σsub := subs_plus_r hb.σsub
    σle := Or.inr (lt_of_le_of_ltY hP.σF hbF h hb.σle (lt_plus_rightY h))
    pos := fun ξ hξ hξσ h0 => ?_
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => ?_
    ge := fun ξ hξ hξσ => ?_
    gap := fun ξ v hξ hξσ hv hne hlt => ?_
    gapP := fun hp => by simp [isPrincipal] at hp
    lclo := fun x β hx hxt hβ hβ0 hβσ hfr => ?_
    nsucc := fun ξ hξ hξσ hns hne => ?_
    bge := fun ξ hξ hξσ => by
      rw [fundBig_plus]
      exact le_transY (wnf_base hP.σF hb.σreg) (hP.nf ξ hξ hξσ) (wnf_oadd ha (hP.nf ξ hξ hξσ))
        (hb.bge ξ hξ hξσ) (le_oadd_right ha (hP.nf ξ hξ hξσ))
    lbK := fun m' e hlt ξ hξ hξσ => by
      subst e
      have hMF := hP.σF
      have hle : Le (.M m') a := le_of_not_ltY ha hMF (fun h' =>
        Lt.asymmY hMF h hlt ((lt_plus_prin_iffY h rfl).mpr h'))
      rw [fundBig_plus]
      exact le_transY hMF ha (wnf_oadd ha (hP.nf ξ hξ hξσ)) hle (le_oadd_leftW ha (hP.nf ξ hξ hξσ))
    lbS := fun m' e hlt ξ hξ hξσ => by
      subst e
      have hSF := WNF.succM hP.σF.M
      have hle : Le (succM m') a := le_of_not_ltY ha hSF (fun h' =>
        Lt.asymmY hSF h hlt ((lt_plus_prin_iffY h rfl).mpr h'))
      rw [fundBig_plus]
      exact le_transY hSF ha (wnf_oadd ha (hP.nf ξ hξ hξσ)) hle (le_oadd_leftW ha (hP.nf ξ hξ hξσ))
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      rw [fundBig_plus] at hC ⊢
      have hyη := hP.nf η hη hησ
      have hη0 : fundBig b η ≠ .zero := by
        intro e
        have h1 := hb.ge η hη hησ
        rw [e] at h1
        rcases h1 with e' | h1
        · rw [e'] at hξη; exact not_lt_zero _ hξη
        · exact not_lt_zero _ h1
      have hp1 := wnf_plus_of_lt h hyη hη0 (hP.lt η hη hησ)
      rw [oadd_plus hp1, inC_plus, Bool.and_eq_true] at hC
      exact inC_oadd ha (hP.nf ξ hξ (lt_transY hξ hη hP.σF hξη hησ)) hC.1
        (hb.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC.2)
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [fundBig_plus] at hC
      exact hb.bw g d ξ L hd hξ hξσ hL hσL (inC_of_oadd_right ha (hP.nf ξ hξ hξσ) hC) }
  · rw [fundBig_plus] at h0
    exact absurd h0 (oadd_ne_zero_left ha (hP.nf ξ hξ hξσ) ha0)
  · rw [inC_plus, Bool.and_eq_true] at hC
    exact hb.σC g d hd hC.2
  · rw [inC_plus, Bool.and_eq_true] at hC
    rw [fundBig_plus]
    exact inC_oadd ha (hP.nf ξ hξ hξσ) hC.1 (hb.ub g d ξ hg hg0 hd hξ hξσ hbC hC.2 hξC)
  · rw [fundBig_plus] at hC
    exact hb.lo g d ξ hd hξ hξσ (inC_of_oadd_right ha (hP.nf ξ hξ hξσ) hC)
  · rw [fundBig_plus]
    exact le_transY hξ (hP.nf ξ hξ hξσ) (wnf_oadd ha (hP.nf ξ hξ hξσ)) (hb.ge ξ hξ hξσ)
      (le_oadd_right ha (hP.nf ξ hξ hξσ))
  · rw [fundBig_plus]
    exact gap_plus h (hP.nf ξ hξ hξσ) (hb.gap ξ · hξ hξσ) v hv hne hlt
  · rw [fundBig_plus]
    have hyF := hP.nf β hβ hβσ
    rcases lt_plus_cases h hx hxt with hle | ⟨y, rfl, hy, hyb⟩
    · have hy0 : fundBig b β ≠ .zero := by
        intro e
        have h1 := hb.ge β hβ hβσ
        rw [e] at h1
        rcases h1 with e' | h1
        · exact absurd hβ0 (by rw [e']; exact Lt.irrefl _)
        · exact not_lt_zero _ h1
      exact lt_of_le_of_ltY hx ha (wnf_oadd ha hyF) hle (lt_oadd_left ha hyF hy0)
    · rw [← oadd_plus hx]
      refine oadd_lt_oadd ha hy hyF (hb.lclo y β hy hyb hβ hβ0 hβσ (fun f hf => ?_))
      by_cases hxσ : Lt (.plus a y) σ
      · have h1 := hfr _ (by rw [lfr_of_lt hxσ]; exact List.mem_singleton.mpr rfl)
        exact lt_of_le_of_ltY (hy.of_mem_subs (lfr_spec hf).1) hx hβ
          (le_transY (hy.of_mem_subs (lfr_spec hf).1) hy hx (lfr_le hP.σF hy hf)
            (Or.inr (lt_plus_rightY hx))) h1
      · exact hfr f ((mem_lfr_plus hxσ).mpr (Or.inr hf))
  · rw [fundBig_plus]
    have hyF := hP.nf ξ hξ hξσ
    by_cases h0 : fundBig b ξ = .zero
    · rw [h0, oadd_zero, isSucc_principal hap]
      obtain ⟨n, rfl⟩ := eq_M_of_subs_self hb0 (hb.pos ξ hξ hξσ h0)
      have hle := WNF.plus_head h (show summands (Tm.M n) = [.M n] from rfl)
      intro e
      have e' : a = one := beq_iff_eq.mp e
      subst e'
      have hn := hbF.M
      exact not_lt_of_leY hbF WNF.one (le_of_ne_gtY hbF WNF.one hle)
        (lt_of_lev_lt' (by simp only [lev, one, Nat.max_eq_left (Nat.zero_le 1)]; omega))
    · rw [isSucc_oadd ha hyF h0]
      exact hb.nsucc ξ hξ hξσ hns hne

theorem inv_plus {a b : Tm} (h : WNF (.plus a b)) (hb : Inv b) : Inv (.plus a b) :=
  ⟨fun hd => natInv_plus h (hb.1 (by rwa [dom_plus] at hd)),
    fun σ hd => bigInv_plus h (hb.2 σ (by rwa [dom_plus] at hd))⟩

/-! ### 正則項 -/

/-- 始点 `b` が `t` の真の部分項（`t` 未満のもの）より大きければ、`t[ξ] = b ⊕ ξ` の列は不変量を満たす -/
theorem bigInv_reg {t b : Tm} (ht : WNF t) (htp : isPrincipal t = true) (ht0 : t ≠ .zero)
    (hreg : IsRegY t) (hb : WNF b) (hbt : Lt b t) (hf : ∀ ξ, fundBig t ξ = oadd b ξ)
    (hbase : base t = b) (hgap : ∀ v, v ∈ subs t → v ≠ t → Lt v t → Lt v b)
    (hpos : b = .zero → ∀ v, v ∈ subs t → v = t)
    (hbs : t ≠ .Om .zero → ¬ isSucc b = true) : BigInv t t := by
  have hPr := bigProps_reg ht htp ht0 hb hbt hf
  refine {
    props := hPr
    σreg := hreg
    σsub := self_mem_subs t
    σle := Or.inl rfl
    pos := fun ξ hξ _ h0 => ?_
    σC := fun _ _ _ h => h
    ub := fun g d ξ _ _ _ hξ _ hbC _ hξC => ?_
    lo := fun g d ξ _ hξ _ hC => ?_
    ge := fun ξ hξ _ => ?_
    gap := fun ξ v hξ _ hv hne hlt => ?_
    gapP := fun _ ξ v hξ _ hv hne hlt => ?_
    lclo := fun x β hx hxt hβ _ _ hfr => ?_
    nsucc := fun ξ hξ _ hns hne => ?_
    bge := fun ξ hξ _ => by rw [hf, hbase]; exact le_oadd_leftW hb hξ
    lbK := fun m e hlt _ _ _ => by subst e; exact absurd hlt (Lt.irrefl _)
    lbS := fun m e hlt _ _ _ => by
      subst e
      exact absurd hlt (Lt.asymmY ht (WNF.succM ht.M) (M_lt_succM ht.M))
    ub2 := fun g d ξ η _ _ _ hξ _ _ _ hbC hξC _ => by
      rw [hf]
      rcases hbC with hbC | hbξ
      · rw [hbase] at hbC; exact inC_oadd hb hξ hbC hξC
      · have hbp := base_zero_or_prin hreg
        rw [hbase] at hbξ hbp
        exact inC_oadd_le hb hbp hξ hbξ hξC
    bw := fun g d ξ L _ hξ hξσ hL hσL hC =>
      ⟨fundBig t ξ, hPr.nf ξ hξ hξσ, hC, by rw [hf, hbase]; exact le_oadd_leftW hb hξ,
        lt_transY (hPr.nf ξ hξ hξσ) ht hL (hPr.lt ξ hξ hξσ) hσL⟩ }
  · rw [hf] at h0
    apply hpos
    rcases le_oadd_leftW hb hξ with e | hlt
    · rw [e]; exact h0
    · rw [h0] at hlt; exact absurd hlt (not_lt_zero _)
  · rw [hf]; rw [hbase] at hbC; exact inC_oadd hb hξ hbC hξC
  · rw [hf] at hC; exact inC_of_oadd_right hb hξ hC
  · rw [hf]; exact le_oadd_right hb hξ
  · rw [hf]
    exact Or.inr (lt_of_lt_of_leY (ht.of_mem_subs hv) hb (wnf_oadd hb hξ) (hgap v hv hne hlt)
      (le_oadd_leftW hb hξ))
  · rw [hf]
    exact lt_of_lt_of_leY (ht.of_mem_subs hv) hb (wnf_oadd hb hξ) (hgap v hv hne hlt)
      (le_oadd_leftW hb hξ)
  · rw [hf]
    have h1 := hfr x (by rw [lfr_of_lt hxt]; exact List.mem_singleton.mpr rfl)
    exact lt_of_lt_of_leY hx hβ (wnf_oadd hb hβ) h1 (le_oadd_right hb hβ)
  · rw [hf]
    by_cases h0 : ξ = .zero
    · subst h0
      rw [oadd_zero]
      rcases hne with h' | h'
      · exact absurd rfl h'
      · exact hbs h'
    · rw [isSucc_oadd hb hξ h0]; exact hns

theorem inv_M {n : Nat} (h : WNF (.M n)) : Inv (.M n) := by
  refine ⟨(fun hd => by rw [dom_M] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_M] at hd
  cases hd
  have hsub : ∀ v, v ∈ subs (Tm.M n) → v = .M n := fun v hv => by
    simpa [subs] using hv
  exact bigInv_reg h rfl (by intro e; cases e) (IsRegY.M n) (wnf_kTerm _) (kTerm_lt_M h.M)
    (fundBig_M n) rfl (fun v hv hne _ => absurd (hsub v hv) hne) (fun _ => hsub)
    (fun _ => by unfold kTerm; split <;> simp [isSucc, summands, one])

theorem isRegY_of_omReg {c : Tm} (hs : omReg c) : IsRegY (.Om c) := IsRegY.tgt (isTgt_of_omReg hs)

theorem inv_om_reg {c : Tm} (h : WNF (.Om c)) (hs : omReg c) : Inv (.Om c) := by
  refine ⟨(fun hd => by rw [dom_om_reg hs] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_om_reg hs] at hd
  cases hd
  refine bigInv_reg h rfl (by intro e; cases e) (isRegY_of_omReg hs) (wnf_base_om h hs)
    (base_om_lt c) (fundBig_om_reg hs) rfl (fun v hv hne hlt => ?_) (fun e => by cases e)
    (fun hne he => hne (by simp [base, isSucc, summands, one] at he; rw [he]))
  have hvc : v ∈ subs c := by
    simp only [subs, List.mem_cons] at hv
    rcases hv with e | hv
    · exact absurd e hne
    · exact hv
  exact sub_lt_base_om h hs .zero v hvc (h.of_mem_subs hv) hlt

theorem inv_xi {n : Nat} {d : Tm} (h : WNF (.Xi n d)) : Inv (.Xi n d) := by
  refine ⟨(fun hd => by rw [dom_xi] at hd; cases hd), fun σ hd => ?_⟩
  rw [dom_xi] at hd
  cases hd
  refine bigInv_reg h rfl (by intro e; cases e) (Or.inr (Or.inr (Or.inr ⟨n, d, rfl⟩)))
    (wnf_base_xi h) (psi_xi_lt_xi n d _) (fundBig_xi n d) rfl (fun v hv hne hlt => ?_)
    (fun e => by cases e) (fun _ he => by simp [base, isSucc, summands, one] at he)
  have hvd : v ∈ subs d := by
    simp only [subs, List.mem_cons] at hv
    rcases hv with e | hv
    · exact absurd e hne
    · exact hv
  exact sub_lt_base_xi h _ v hvd (h.of_mem_subs hv) hlt

/-! ### `Ω_c`（`c` 極限） -/

/-- 次の正則項 `Ω_e` の添字 `e` は、`0` か、`v` の部分項か、`v` の部分項の後者 -/
theorem nrY_idx : ∀ v : Tm, ∃ e, nrY v = .Om e ∧
    (e = .zero ∨ e ∈ subs v ∨ ∃ w, w ∈ subs v ∧ e = succT w)
  | .zero => ⟨.zero, rfl, Or.inl rfl⟩
  | .plus a b => by
    obtain ⟨e, he, h⟩ := nrY_idx a
    refine ⟨e, he, ?_⟩
    rcases h with h | h | ⟨w, hw, hwe⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (subs_plus_l h))
    · exact Or.inr (Or.inr ⟨w, subs_plus_l hw, hwe⟩)
  | .Om a => ⟨succT a, rfl, Or.inr (Or.inr ⟨a, subs_om (self_mem_subs a), rfl⟩)⟩
  | .M n => ⟨succT (.M n), rfl, Or.inr (Or.inr ⟨.M n, self_mem_subs _, rfl⟩)⟩
  | .Xi n a => ⟨succT (.Xi n a), rfl, Or.inr (Or.inr ⟨.Xi n a, self_mem_subs _, rfl⟩)⟩
  | .Psi π β => by
    cases π with
    | Om c => exact ⟨c, rfl, Or.inr (Or.inl (subs_psi_p (subs_om (self_mem_subs c))))⟩
    | zero => exact ⟨_, rfl, Or.inr (Or.inr ⟨_, self_mem_subs _, rfl⟩)⟩
    | M n => exact ⟨_, rfl, Or.inr (Or.inr ⟨_, self_mem_subs _, rfl⟩)⟩
    | plus a b => exact ⟨_, rfl, Or.inr (Or.inr ⟨_, self_mem_subs _, rfl⟩)⟩
    | Xi n a => exact ⟨_, rfl, Or.inr (Or.inr ⟨_, self_mem_subs _, rfl⟩)⟩
    | Psi p q => exact ⟨_, rfl, Or.inr (Or.inr ⟨_, self_mem_subs _, rfl⟩)⟩

/-- `Ω_c`（`c` 極限）の隙間：`c` の隙間（等号つき）から、`Ω_c` の真の部分項で `Ω_c` 未満のものは
    `Ω_{y+1}` 未満 -/
theorem gap_om {c y : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hy : WNF y)
    (G : ∀ v, v ∈ subs c → v ≠ c → Lt v c → Le v y) :
    ∀ v, v ∈ subs (.Om c) → v ≠ .Om c → Lt v (.Om c) → Lt v (.Om (succT y)) := by
  have hcF := h.om.1
  intro v hv hne hlt
  have hvc : v ∈ subs c := by
    simp only [subs, List.mem_cons] at hv
    rcases hv with e | hv
    · exact absurd e hne
    · exact hv
  have hvF := hcF.of_mem_subs hvc
  obtain ⟨e, he, hidx⟩ := nrY_idx v
  obtain ⟨hnF, hnR, hvn⟩ := nr_specY v hvF
  have hle : Le (nrY v) (.Om c) := nr_le_omY v hvF c h hlt
  rw [he] at hnF hnR hvn hle
  have heF := hnF.om.1
  have hec : Lt e c := by
    rcases hle with e' | hlt'
    · exfalso
      cases e'
      apply hs
      rcases hnR with h1 | ⟨c', h1, h2⟩ | ⟨n, h1⟩ | ⟨n, p, h1⟩
      · cases h1; exact Or.inl rfl
      · cases h1; exact Or.inr h2
      · cases h1
      · cases h1
    · exact lt_om_iffG.mp hlt'
  have hsy := succT_WNF hy
  have hey : Le e (succT y) := by
    rcases hidx with e0 | hes | ⟨w, hw, hwe⟩
    · rw [e0]; exact zero_le _
    · have hesc : e ∈ subs c := subs_trans hvc hes
      exact Or.inr (lt_of_le_of_ltY heF hy hsy (G e hesc (Lt.ne hec) hec) (lt_succT y))
    · have hwc : w ∈ subs c := subs_trans hvc hw
      have hwF := hcF.of_mem_subs hwc
      have hwe' : Lt w e := by rw [hwe]; exact lt_succT w
      have hwlt : Lt w c := lt_transY hwF heF hcF hwe' hec
      rcases G w hwc (Lt.ne hwlt) hwlt with e1 | h1
      · rw [hwe, e1]; exact Or.inl rfl
      · rw [hwe]; exact Or.inr (succT_lt_succT hwF hy h1)
  exact lt_of_lt_of_leY hvF hnF (WNF.om_succT hy) hvn (le_om_of_leY hey)

theorem natInv_om {c : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : NatInv c) : NatInv (.Om c) := by
  refine ⟨natProps_om h hs hc.props, fun n => ?_, fun g d n hg hg0 hd hC => ?_,
    fun n v hv hne hlt => ?_, fun g d n hg hg0 hd hC => ?_⟩
  · rw [fundNat_om hs]; intro e; cases e
  · rw [inC_om] at hC
    rw [fundNat_om hs, inC_om]
    exact inC_succT (inC_one hg0) (hc.ub g d n hg hg0 hd hC)
  · rw [fundNat_om hs]
    exact gap_om h hs (hc.props.nf n) (fun v hv hne hlt => Or.inr (hc.gap n v hv hne hlt)) v hv hne hlt
  · rw [fundNat_om hs, inC_om] at hC
    rw [fundNat_om hs, inC_om]
    exact inC_succT (inC_one hg0) (hc.ub2 g d n hg hg0 hd (inC_of_succT hC))

theorem bigInv_om {c σ : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : BigInv c σ) :
    BigInv (.Om c) σ := by
  have hcF := h.om.1
  have hP := hc.props
  have hgapS : ∀ ξ v, WNF ξ → Lt ξ σ → v ∈ subs (Tm.Om c) → v ≠ .Om c → Lt v (.Om c) →
      Lt v (fundBig (.Om c) ξ) := by
    intro ξ v hξ hξσ hv hne hlt
    rw [fundBig_om_lim hs]
    exact gap_om h hs (hP.nf ξ hξ hξσ) (hc.gap ξ · hξ hξσ) v hv hne hlt
  refine {
    props := bigProps_om h hs hP
    σreg := hc.σreg
    σsub := subs_om hc.σsub
    σle := Or.inr (lt_of_le_of_ltY hP.σF hcF h hc.σle (lt_om_selfY h))
    pos := fun ξ _ _ h0 => ?_
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => ?_
    ge := fun ξ hξ hξσ => ?_
    gap := fun ξ v hξ hξσ hv hne hlt => Or.inr (hgapS ξ v hξ hξσ hv hne hlt)
    gapP := fun _ ξ v hξ hξσ hv hne hlt => hgapS ξ v hξ hξσ hv hne hlt
    lclo := fun x β hx hxt hβ hβ0 hβσ hfr => ?_
    nsucc := fun ξ _ _ _ _ => by rw [fundBig_om_lim hs]; simp [isSucc, summands, one]
    bge := fun ξ hξ hξσ => by
      rw [fundBig_om_lim hs]
      have hyF := hP.nf ξ hξ hξσ
      exact Or.inr (lt_of_le_of_ltY (wnf_base hP.σF hc.σreg) hyF (WNF.om_succT hyF)
        (hc.bge ξ hξ hξσ) (lt_succT_om hyF))
    lbK := fun m e hlt ξ hξ hξσ => by
      subst e
      have hMF := hP.σF
      have hm := hMF.M
      rw [fundBig_om_lim hs]
      have h1 : Lt (.M m) c := (lt_M_omY hm h).mp hlt
      have h2 := hc.lbK m rfl h1 ξ hξ hξσ
      have hyF := hP.nf ξ hξ hξσ
      exact Or.inr ((lt_M_omY hm (WNF.om_succT hyF)).mpr
        (lt_of_le_of_ltY hMF hyF (succT_WNF hyF) h2 (lt_succT _)))
    lbS := fun m e hlt ξ hξ hξσ => by
      subst e
      have hMF := hP.σF
      rw [fundBig_om_lim hs]
      have h1 : Lt (succT (.M m)) c := lt_om_iffG.mp hlt
      have h1' : Lt (.M m) c := lt_transY hMF (succT_WNF hMF) hcF (lt_succT _) h1
      have h2 := hc.lbK m rfl h1' ξ hξ hξσ
      have hyF := hP.nf ξ hξ hξσ
      show Le (.Om (succT (.M m))) (.Om (succT (fundBig c ξ)))
      rcases h2 with e | h2
      · rw [← e]; exact Or.inl rfl
      · exact Or.inr (lt_om_iffG.mpr (succT_lt_succT hMF hyF h2))
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      rw [fundBig_om_lim hs, inC_om] at hC
      rw [fundBig_om_lim hs, inC_om]
      exact inC_succT (inC_one hg0) (hc.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC (inC_of_succT hC))
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [fundBig_om_lim hs, inC_om] at hC
      exact hc.bw g d ξ L hd hξ hξσ hL hσL (inC_of_succT hC) }
  rotate_right
  · rw [fundBig_om_lim hs]
    have hyF := hP.nf β hβ hβσ
    have hsF : WNF (succT (fundBig c β)) := succT_WNF hyF
    have hO : WNF (.Om (succT (fundBig c β))) := WNF.om_succT hyF
    have hyO : Lt (fundBig c β) (.Om (succT (fundBig c β))) := lt_succT_om hyF
    have hσF := hP.σF
    show Lt x (.Om (succT (fundBig c β)))
    by_cases hxσ : Lt x σ
    · have h1 := hfr x (by rw [lfr_of_lt hxσ]; exact List.mem_singleton.mpr rfl)
      exact lt_transY hx hyF hO (lt_of_lt_of_leY hx hβ hyF h1 (hc.ge β hβ hβσ)) hyO
    cases hsx : summands x with
    | nil => rw [eq_zero_of_summands_nil hsx]; exact zero_lt (by intro e; cases e)
    | cons u r =>
      have huW := summands_WNF x hx u (by rw [hsx]; exact List.mem_cons_self)
      have huF := huW.1
      have hup := huW.2
      have hul : Lt u (.Om c) := lt_of_le_of_ltY huF hx h (head_leY hx hsx) hxt
      have huσ : ¬ Lt u σ := fun h' => hxσ (lt_of_head_lt (IsRegY.principal hc.σreg) hsx
        ((lt_principal_iff hup (IsRegY.principal hc.σreg)).mp h'))
      have hfu : ∀ f, f ∈ lfr σ u → Lt f β := by
        intro f hf
        refine hfr f ?_
        cases x with
        | zero => simp [summands] at hsx
        | plus a b =>
          simp only [summands, List.cons.injEq] at hsx
          rw [← hsx.1] at hf
          exact (mem_lfr_plus hxσ).mpr (Or.inl hf)
        | _ =>
          simp only [summands, List.cons.injEq] at hsx
          rw [hsx.1]; exact hf
      refine lt_of_head_lt rfl hsx ((lt_principal_iff hup rfl).mp ?_)
      have hcl : ∀ z, WNF z → Lt z c → (∀ f, f ∈ lfr σ z → Lt f β) → Lt z (fundBig c β) :=
        fun z hz hzc hzf => hc.lclo z β hz hzc hβ hβ0 hβσ hzf
      cases u with
      | zero => cases hup
      | plus _ _ => cases hup
      | M n =>
        have hn := huF.M
        have h1 : Lt (.M n) c := (lt_M_omY hn h).mp hul
        have h2 := hcl _ huF h1 (fun f hf => by simp [lfr, huσ] at hf)
        exact (lt_M_omY hn hO).mpr (lt_transY huF hyF hsF h2 (lt_succT _))
      | Om d =>
        have hdF := huF.om.1
        have h1 : Lt d c := lt_om_iffG.mp hul
        have h2 := hcl d hdF h1 (fun f hf => hfu f ((mem_lfr_om huσ).mpr hf))
        exact lt_om_iffG.mpr (lt_transY hdF hyF hsF h2 (lt_succT _))
      | Xi n a =>
        have hOF : IsOF (.Xi n a) := Or.inl ⟨n, a, rfl⟩
        have h1 : Lt (.Xi n a) c := (lt_OF_omY hOF huF hcF).mp hul
        have h2 := hcl _ huF h1 hfu
        exact (lt_OF_omY hOF huF hsF).mpr (lt_transY huF hyF hsF h2 (lt_succT _))
      | Psi ρ a =>
        have hQ := huF.psi
        rcases hQ.tgt with rfl | ⟨d, rfl, hds⟩ | ⟨n, p, rfl⟩
        · exact (lt_psiOm_omY huF hsF).mpr (zero_le _)
        · have hdF := hQ.piF.om.1
          have h1 : Le d c := (lt_psiOm_omY huF hcF).mp hul
          have h1' : Lt d c := by
            rcases h1 with e | h1
            · exact absurd (Or.inr (e ▸ hds)) hs
            · exact h1
          have hρσ : ¬ Lt (.Om d) σ := fun h' =>
            huσ (lt_transY huF hQ.piF hσF (lt_psi_targetY huF) h')
          have h2 := hcl d hdF h1' (fun f hf => hfu f
            ((mem_lfr_psi huσ).mpr (Or.inl ((mem_lfr_om hρσ).mpr hf))))
          exact (lt_psiOm_omY huF hsF).mpr (Or.inr (lt_transY hdF hyF hsF h2 (lt_succT _)))
        · have hOF : IsOF (Tm.Psi (.Xi n p) a) := Or.inr ⟨n, p, a, rfl⟩
          have h1 : Lt (Tm.Psi (.Xi n p) a) c := (lt_OF_omY hOF huF hcF).mp hul
          have h2 := hcl _ huF h1 hfu
          exact (lt_OF_omY hOF huF hsF).mpr (lt_transY huF hyF hsF h2 (lt_succT _))
  · rw [fundBig_om_lim hs] at h0; cases h0
  · rw [inC_om] at hC; exact hc.σC g d hd hC
  · rw [inC_om] at hC
    rw [fundBig_om_lim hs, inC_om]
    exact inC_succT (inC_one hg0) (hc.ub g d ξ hg hg0 hd hξ hξσ hbC hC hξC)
  · rw [fundBig_om_lim hs, inC_om] at hC
    exact hc.lo g d ξ hd hξ hξσ (inC_of_succT hC)
  · rw [fundBig_om_lim hs]
    have hyF := hP.nf ξ hξ hξσ
    exact Or.inr (lt_of_le_of_ltY hξ hyF (WNF.om_succT hyF) (hc.ge ξ hξ hξσ) (lt_succT_om hyF))

theorem inv_om_lim {c : Tm} (h : WNF (.Om c)) (hs : ¬ omReg c) (hc : Inv c) : Inv (.Om c) :=
  ⟨fun hd => natInv_om h hs (hc.1 (by rwa [dom_om_lim hs] at hd)),
    fun σ hd => bigInv_om h hs (hc.2 σ (by rwa [dom_om_lim hs] at hd))⟩

/-! ### 全ての標準形 -/

/-- 崩壊 `Ψ_π(X)` の列の不変量（真の部分項の不変量を使ってよい） -/
def PsiInv : Prop :=
  ∀ π X, WNF (.Psi π X) → (∀ u, u.size < (Tm.Psi π X).size → WNF u → Inv u) → Inv (.Psi π X)

/-- 崩壊の場合から、全ての標準形の列の不変量 -/
theorem inv_all (hψ : PsiInv) : ∀ t : Tm, WNF t → Inv t := by
  intro t
  induction t using size_induction with
  | h t ih =>
  intro ht
  cases t with
  | zero => exact ⟨(fun hd => by cases hd), (fun σ hd => by cases hd)⟩
  | M n => exact inv_M ht
  | plus a b =>
    obtain ⟨-, hb, -, -⟩ := ht.plus
    exact inv_plus ht (ih b (by simp only [Tm.size]; omega) hb)
  | Om c =>
    by_cases hs : omReg c
    · exact inv_om_reg ht hs
    · exact inv_om_lim ht hs (ih c (by simp only [Tm.size]; omega) ht.om.1)
  | Xi n d => exact inv_xi ht
  | Psi π X => exact hψ π X ht (fun u hu huF => ih u hu huF)

end MahloOCF.FS
