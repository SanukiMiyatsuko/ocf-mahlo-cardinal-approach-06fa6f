import Mahlo.FS.Final

/-! 基本列の反復で得られる順序数項（NOT）と、可算な標準形全体の一致（Compact リポジトリの
`Compact/FS/NotNF.lean` と同じステートメント）。

Subsp の `FundSys.NOT` と同じく、極限となる始点 `notBase n` から基本列 `t ↦ t[n]`（`n` は自然数）を繰り返して
得られる標準形を順序数項（`IsOT`）とし、その全体を `NOT` とする。この系の最初の非可算基数は `Ω_0`
（`Ψ_{Ω_0}(0) = 1`）なので、可算な標準形は `Ω_0` 未満の標準形。

* 始点 `notBase n = Ψ_{Ω_0}(M_{n+1})`：可算な標準形で、共終数は `ω`（極限、`dom_notBase`）。可算な標準形の
  中で共終（可算な `t` は、`n` を部分項の階の最大値に取ると `Ψ_{Ω_0}(M_{n+1})` 未満、`lt_notBase`）。
* 可算な項の共終数は `0`・`1`・`ω` のいずれか（`dom_countable`）：正則項は全て `Ω_0` 以上なので
  （`om_zero_le_reg`）、共終数が正則項 `σ` の項は `σ` 以上、すなわち非可算。
* `isOT_iff`：`IsOT t ⟺ t < Ω_0`。`NOT_eq`：`NOT` は可算な標準形全体 `{t : NF // t < Ω_0}` に等しい。
  `⊆` は基本列が項を増やさないことから、`⊇` は始点の共終性と、基本列の共終性・整列性による下への閉包から。
* `NOTFundLt_iff_lt`：基本列の一歩（`NOTStep`）の推移閉包は、項の順序と一致する。
* `countable_iff_reach`：可算な標準形全体は、可算な極限の始点から基本列の一歩の推移閉包で到達できる元の全体。

基本列は `fsNF` のもの（`fundNF props_all`、`fsNF_fund`）。Bachmann 性は使わない（基本列の降下・共終性と
整列性 `wellFounded_isNF` だけを使う）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 可算な項の共終数 -/

/-- 正則項は `Ω_0` 以上 -/
theorem om_zero_le_reg {σ : Tm} (hσ : WNF σ) (h : IsRegY σ) : Le (.Om .zero) σ := by
  rcases h with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact Or.inl rfl
  · -- `Ω_c`（`c` は後者なので `0` でない）
    have hc0 : c ≠ .zero := by
      rintro rfl
      simp [isSucc, summands] at hs
    exact Or.inr (lt_om_iffG.mpr (zero_lt hc0))
  · -- `M_n`：`Ω_0` の階は `1`
    exact Or.inr ((lt_M_iffY WNF.om_zero hσ.M).mpr (Nat.max_le.mpr ⟨hσ.M, Nat.zero_le _⟩))
  · -- `Ξ_n(p)`：`Ω` の不動点
    exact Or.inr ((lt_om_OFG (Or.inl ⟨n, p, rfl⟩) hσ).mpr (zero_lt (by intro e; cases e)))

/-- 共終数が正則項の項は `Ω_0` 以上（共終数は項以下の正則項） -/
theorem om_zero_le_of_big {t σ : Tm} (ht : WNF t) (h : dom t = .big σ) : Le (.Om .zero) t := by
  have hB := (inv_of t ht).2 σ h
  exact le_transY WNF.om_zero hB.props.σF ht (om_zero_le_reg hB.props.σF hB.σreg) hB.σle

/-- 可算な項の共終数は `0`・`1`・`ω` のいずれか -/
theorem dom_countable {t : Tm} (ht : WNF t) (hc : Lt t (.Om .zero)) :
    dom t = .zero ∨ dom t = .one ∨ dom t = .omega := by
  cases hd : dom t with
  | zero => exact Or.inl rfl
  | one => exact Or.inr (Or.inl rfl)
  | omega => exact Or.inr (Or.inr rfl)
  | big σ => exact absurd hc (not_lt_of_leY WNF.om_zero ht (om_zero_le_of_big ht hd))

/-! ### 基本列の降下と共終性 -/

theorem fund_zero (ξ : Tm) : fund .zero ξ = .zero := rfl

/-- `0` でない項の基本列の項は自分未満 -/
theorem fund_lt_of_ne_zero {t ξ : Tm} (ht : WNF t) (hξ : WNF ξ) (h0 : t ≠ .zero) :
    Lt (fund t ξ) t := by
  have hP := props_all t ht
  rw [fund_eq]
  cases hd : dom t with
  | zero => exact absurd ((dom_eq_zero_iff ht).mp hd) h0
  | one => exact pred_lt ht ((dom_eq_one_iff ht).mp hd)
  | omega => exact (hP.1 hd).lt _
  | big σ =>
    have hB := hP.2 σ hd
    show Lt (fundBig t (if ltB ξ σ = true then ξ else .zero)) t
    by_cases h : ltB ξ σ = true
    · rw [ite_eq_left h]
      exact hB.lt ξ hξ (ltB_iff.mp h)
    · rw [ite_eq_right h]
      exact hB.lt _ WNF.zero hB.pos

/-- 可算な項の基本列は下から共終：`b < a < Ω_0` なら `b ≤ a[n]` となる自然数 `n` がある -/
theorem fund_cof_countable {a b : Tm} (ha : WNF a) (hb : WNF b) (hc : Lt a (.Om .zero)) (h : Lt b a) :
    ∃ n : Nat, Le b (fund a (ofNatT n)) := by
  rcases dom_countable ha hc with hd | hd | hd
  · rw [(dom_eq_zero_iff ha).mp hd] at h
    exact absurd h (not_lt_zero b)
  · refine ⟨0, ?_⟩
    rw [fund_of_dom_one _ hd]
    exact le_pred ha ((dom_eq_one_iff ha).mp hd) hb h
  · obtain ⟨n, hn⟩ := ((props_all a ha).1 hd).cof b hb h
    exact ⟨n, by rw [fund_omega hd]; exact hn⟩

/-! ### 始点 -/

/-- 始点 `Ψ_{Ω_0}(M_{n+1})` -/
def notBase (n : Nat) : Tm := .Psi (.Om .zero) (.M (n + 1))

theorem wnf_notBase (n : Nat) : WNF (notBase n) :=
  WNF.mk_psi ⟨Or.inl rfl, WNF.om_zero, WNF.M' (Nat.le_add_left 1 n), (fun _ _ e => by cases e),
    inC_M _ _ _⟩

/-- 始点は可算 -/
theorem notBase_lt (n : Nat) : Lt (notBase n) (.Om .zero) := lt_psi_targetY (wnf_notBase n)

/-- 始点は極限：共終数は `ω` -/
theorem dom_notBase (n : Nat) : dom (notBase n) = .omega := by
  rcases dom_countable (wnf_notBase n) (notBase_lt n) with hd | hd | hd
  · cases (dom_eq_zero_iff (wnf_notBase n)).mp hd
  · have hs := (dom_eq_one_iff (wnf_notBase n)).mp hd
    simp [notBase, isSucc, summands, one] at hs
  · exact hd

/-- 部分項の階の最大値 -/
def maxLev (t : Tm) : Nat := ((subs t).map lev).foldr max 0

theorem le_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.foldr max 0
  | [], _, h => by cases h
  | a :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem lev_le_maxLev {t v : Tm} (h : v ∈ subs t) : lev v ≤ maxLev t :=
  le_foldr_max (List.mem_map.mpr ⟨v, h, rfl⟩)

/-- 部分項の階が全て `n` 以下の項は `C(M_{n+1}, d)` に入る（節点の引数は全て `M_{n+1}` 未満） -/
theorem inC_of_lev {n : Nat} {d : Tm} : ∀ {t : Tm}, WNF t → (∀ v, v ∈ subs t → lev v ≤ n) →
    inC t (.M (n + 1)) d = true
  | .zero, _, _ => inC_zero _ _
  | .M _, _, _ => inC_M _ _ _
  | .plus a b, ht, h => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨inC_of_lev ha fun v hv => h v (subs_plus_l hv),
      inC_of_lev hb fun v hv => h v (subs_plus_r hv)⟩
  | .Om a, ht, h => by
    rw [inC_om]
    exact inC_of_lev ht.om.1 fun v hv => h v (subs_om hv)
  | .Xi m a, ht, h => by
    have haF := ht.xi.2.1
    refine inC_xi_iff.mpr (Or.inr ⟨inC_of_lev haF fun v hv => h v (subs_xi hv), ?_⟩)
    exact (lt_M_iffY haF (Nat.le_add_left 1 n)).mpr
      (Nat.le_trans (h a (subs_xi (self_mem_subs a))) (Nat.le_succ n))
  | .Psi p a, ht, h => by
    have hP := ht.psi
    refine inC_psi_iff.mpr (Or.inr ⟨inC_of_lev hP.piF fun v hv => h v (subs_psi_p hv),
      inC_of_lev hP.aF fun v hv => h v (subs_psi_a hv), ?_⟩)
    exact (lt_M_iffY hP.aF (Nat.le_add_left 1 n)).mpr
      (Nat.le_trans (h a (subs_psi_a (self_mem_subs a))) (Nat.le_succ n))

/-- 始点は可算な標準形の中で共終：可算な `t` は、`n` を部分項の階の最大値に取ると `Ψ_{Ω_0}(M_{n+1})` 未満
    （`t` の節点の引数は全て `M_{n+1}` 未満なので `t ∈ C(M_{n+1}, Ψ_{Ω_0}(M_{n+1}))`、崩壊の性質による） -/
theorem lt_notBase {t : Tm} (ht : WNF t) (hc : Lt t (.Om .zero)) : Lt t (notBase (maxLev t)) :=
  coll_psiY (wnf_notBase (maxLev t)) ht (inC_of_lev ht fun _ hv => lev_le_maxLev hv) hc

/-! ### 順序数項（NOT） -/

/-- 自然数（標準形） -/
def ofNatNF (n : Nat) : NF := ⟨ofNatT n, wnf_ofNatT n⟩

/-- `fsNF` の基本列は `fundNF props_all` -/
theorem fsNF_fund (a ξ : NF) : _root_.FS.fund (self := fsNF) a ξ = fundNF props_all a ξ := rfl

/-- `fsNF` の自然数は `ofNatNF` -/
theorem fsNF_ofNat (n : Nat) : _root_.FS.ofNat (self := fsNF) n = ofNatNF n := rfl

/-- 始点（標準形） -/
def baseNF (n : Nat) : NF := ⟨notBase n, wnf_notBase n⟩

/-- 順序数項：始点 `notBase n` から基本列 `t ↦ t[n]`（`n` は自然数）の反復で得られる標準形
    （Subsp の `FundSys.IsOT`） -/
inductive IsOT : NF → Prop
  | base (n : Nat) : IsOT (baseNF n)
  | step (s : NF) : IsOT s → ∀ n : Nat, IsOT (fundNF props_all s (ofNatNF n))

/-- 順序数項の全体（Subsp の `FundSys.NOT`） -/
def NOT := { s : NF // IsOT s }

/-- 始点は極限 -/
theorem domNF_baseNF (n : Nat) : domNF props_all (baseNF n) = .omega :=
  (domNF_omega props_all).mpr (dom_notBase n)

/-- 順序数項は可算 -/
theorem IsOT.lt_om {t : NF} (h : IsOT t) : Lt t.1 (.Om .zero) := by
  induction h with
  | base n => exact notBase_lt n
  | step s _ n ih =>
    show Lt (fund s.1 (ofNatT n)) (.Om .zero)
    by_cases h0 : s.1 = .zero
    · rw [h0, fund_zero]
      rw [h0] at ih
      exact ih
    · exact lt_transY (wnf_fund props_all s.2 (wnf_ofNatT n)) s.2 WNF.om_zero
        (fund_lt_of_ne_zero s.2 (wnf_ofNatT n) h0) ih

/-- 下への閉包：順序数項以下の標準形は順序数項（`a` についての整礎帰納。`b < a` なら、基本列の共終性から
    `b ≤ a[n] < a` となる `n` があり、`a[n]` は順序数項） -/
theorem IsOT.of_le {a : NF} (ha : IsOT a) : ∀ {b : NF}, Le b.1 a.1 → IsOT b := by
  refine WellFounded.induction (C := fun a : NF => IsOT a → ∀ {b : NF}, Le b.1 a.1 → IsOT b)
    wellFounded_isNF a ?_ ha
  intro a ih ha b hb
  rcases hb with e | hlt
  · rw [Subtype.ext e]
    exact ha
  · obtain ⟨n, hn⟩ := fund_cof_countable a.2 b.2 ha.lt_om hlt
    have ha0 : a.1 ≠ .zero := fun e => not_lt_zero b.1 (by rw [← e]; exact hlt)
    exact ih (fundNF props_all a (ofNatNF n)) (fund_lt_of_ne_zero a.2 (wnf_ofNatT n) ha0)
      (.step a ha n) hn

/-- **NOT は可算な標準形全体と一致する**：`IsOT t ⟺ t < Ω_0` -/
theorem isOT_iff (t : NF) : IsOT t ↔ Lt t.1 (.Om .zero) :=
  ⟨IsOT.lt_om, fun hc => (IsOT.base (maxLev t.1)).of_le (Or.inr (lt_notBase t.2 hc))⟩

/-- `NOT` は可算な標準形全体 `{t : NF // t < Ω_0}` に等しい -/
theorem NOT_eq : NOT = { t : NF // Lt t.1 (.Om .zero) } :=
  congrArg Subtype (funext fun t => propext (isOT_iff t))

/-! ### 基本列による順序 -/

/-- 基本列の一歩：`a` は `b` の基本列の項（Subsp の `FundSys.NOTStep`） -/
def NOTStep (a b : NOT) : Prop := b.1.1 ≠ .zero ∧ ∃ n : Nat, a.1 = fundNF props_all b.1 (ofNatNF n)

/-- 基本列の一歩の推移閉包（Subsp の `FundSys.NOTFundLt`） -/
abbrev NOTFundLt : NOT → NOT → Prop := Relation.TransGen NOTStep

/-- 基本列の項はもとの項より小さい（Subsp の `FundDesc`） -/
theorem NOT.fundDesc (b : NOT) (n : Nat) (hb : b.1.1 ≠ .zero) : fundNF props_all b.1 (ofNatNF n) < b.1 :=
  fund_lt_of_ne_zero b.1.2 (wnf_ofNatT n) hb

/-- 基本列は下から共終（Subsp の `FundCofinal`） -/
theorem NOT.fundCofinal (a b : NOT) (h : b.1 < a.1) :
    ∃ n : Nat, b.1 ≤ fundNF props_all a.1 (ofNatNF n) := by
  obtain ⟨n, hn⟩ := fund_cof_countable a.1.2 b.1.2 a.2.lt_om h
  exact ⟨n, nf_le.mpr hn⟩

/-- `NOT` の上の順序は整礎 -/
theorem NOT.wf : WellFounded (fun a b : NOT => a.1 < b.1) :=
  InvImage.wf (fun s : NOT => s.1) wellFounded_isNF

theorem NOTStep.lt {a b : NOT} (h : NOTStep a b) : a.1 < b.1 := by
  obtain ⟨hb, n, e⟩ := h
  rw [e]
  exact NOT.fundDesc b n hb

theorem NOTFundLt.lt {a b : NOT} (h : NOTFundLt a b) : a.1 < b.1 := by
  induction h with
  | single h => exact h.lt
  | @tail c d _ hcd ih => exact lt_transY a.1.2 c.1.2 d.1.2 ih hcd.lt

theorem NOTFundLt_of_lt (b : NOT) : ∀ a : NOT, a.1 < b.1 → NOTFundLt a b := by
  refine NOT.wf.induction (C := fun b : NOT => ∀ a : NOT, a.1 < b.1 → NOTFundLt a b) b ?_
  intro b ih a hab
  have hb0 : b.1.1 ≠ .zero := fun e => not_lt_zero a.1.1 (by rw [← e]; exact hab)
  obtain ⟨n, hn⟩ := NOT.fundCofinal b a hab
  let c : NOT := ⟨fundNF props_all b.1 (ofNatNF n), .step _ b.2 n⟩
  have hstep : NOTStep c b := ⟨hb0, n, rfl⟩
  rcases nf_le.mp hn with e | h
  · have hac : a = c := Subtype.ext (Subtype.ext e)
    rw [hac]
    exact .single hstep
  · exact .tail (ih c hstep.lt a h) hstep

/-- **基本列の一歩の推移閉包と項の順序の一致**（Subsp の `FundSys.NOTFundLt_iff_lt`） -/
theorem NOTFundLt_iff_lt (a b : NOT) : NOTFundLt a b ↔ a.1 < b.1 :=
  ⟨NOTFundLt.lt, NOTFundLt_of_lt b a⟩

/-! ### 可算な極限の始点からの到達 -/

/-- 基本列の一歩（標準形の上）：`a` は `b`（`≠ 0`）の基本列の項 -/
def FundStep (a b : NF) : Prop := b.1 ≠ .zero ∧ ∃ n : Nat, a = fundNF props_all b (ofNatNF n)

theorem FundStep.lt {a b : NF} (h : FundStep a b) : a < b := by
  obtain ⟨hb, n, rfl⟩ := h
  exact fund_lt_of_ne_zero b.2 (wnf_ofNatT n) hb

theorem FundStep.transGen_lt {a b : NF} (h : Relation.TransGen FundStep a b) : a < b := by
  induction h with
  | single h => exact h.lt
  | @tail c d _ hcd ih => exact lt_transY a.2 c.2 d.2 ih hcd.lt

/-- 順序数項の間の基本列の一歩の推移閉包は、標準形の間の推移閉包 -/
theorem NOTFundLt.toNF {a b : NOT} (h : NOTFundLt a b) : Relation.TransGen FundStep a.1 b.1 := by
  induction h with
  | single h => exact .single h
  | tail _ hcd ih => exact .tail ih hcd

/-- **可算な標準形全体は、可算な極限の始点 `Ψ_{Ω_0}(M_{n+1})` から基本列の一歩の推移閉包で到達できる元の全体**：
    `t < Ω_0 ⟺ ∃ n, t ← ⋯ ← Ψ_{Ω_0}(M_{n+1})` -/
theorem countable_iff_reach (t : NF) :
    Lt t.1 (.Om .zero) ↔ ∃ n : Nat, Relation.TransGen FundStep t (baseNF n) := by
  constructor
  · intro hc
    refine ⟨maxLev t.1, ?_⟩
    exact NOTFundLt.toNF (a := ⟨t, (isOT_iff t).mpr hc⟩) (b := ⟨baseNF (maxLev t.1), .base _⟩)
      (NOTFundLt_of_lt _ _ (lt_notBase t.2 hc))
  · rintro ⟨n, h⟩
    exact lt_transY t.2 (wnf_notBase n) WNF.om_zero (FundStep.transGen_lt h) (notBase_lt n)

/-- 可算な標準形の集合と、可算な極限の始点から基本列の推移閉包で到達できる元の集合の一致（集合は述語で表す） -/
theorem countable_eq_reach :
    (fun t : NF => Lt t.1 (.Om .zero)) = fun t => ∃ n : Nat, Relation.TransGen FundStep t (baseNF n) :=
  funext fun t => propext (countable_iff_reach t)

end MahloOCF.FS

/-! `#print axioms` の出力を固定する検査。 -/

/-- info: 'MahloOCF.FS.isOT_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.isOT_iff

/-- info: 'MahloOCF.FS.NOT_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.NOT_eq

/-- info: 'MahloOCF.FS.NOTFundLt_iff_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.NOTFundLt_iff_lt

/-- info: 'MahloOCF.FS.countable_eq_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.countable_eq_reach
