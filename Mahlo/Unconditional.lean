import Mahlo.Complete
import Mahlo.WF.Wmax
import Mahlo.WF.Fund

/-! 大基数の仮定なしの結論。

`Mahlo/Complete.lean` の `wellFounded_lt`・`lt_strictTotal`・`cmp_eq_iff` は弱 Mahlo 基数の列を仮定して
意味論から導いたもの。ここでは同じ主張を、`Mahlo/WF` の構文的な証明（区別集合の方法）から仮定なしに示す。
公理は `propext`・`Quot.sound` だけ（`Classical.choice` も使わない）。 -/

namespace OCF.Mahlo

open MahloOCF

/-- 標準形の上の `lt` は整礎（仮定なし） -/
theorem wellFounded_NFLt : WellFounded NFLt := wellFounded_lt_isNF

/-- 標準形の上の `lt` は狭義全順序（仮定なし） -/
theorem lt_strictTotal_NF :
    (∀ a : NF, ¬ NFLt a a) ∧ (∀ a b c : NF, NFLt a b → NFLt b c → NFLt a c) ∧
      (∀ a b : NF, NFLt a b ∨ a = b ∨ NFLt b a) := by
  have toLt : ∀ {a b : NF}, NFLt a b ↔ Lt a.1 b.1 := by
    intro a b
    unfold NFLt MahloOCF.lt Lt
    simp only [beq_iff_eq]
  refine ⟨fun a h => Lt.irrefl _ (toLt.mp h), fun a b c h1 h2 => ?_, fun a b => ?_⟩
  · exact toLt.mpr (transY a.2 b.2 c.2 (toLt.mp h1) (toLt.mp h2))
  · rcases triY a.2 b.2 with h | h | h
    · exact Or.inl (toLt.mpr h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (toLt.mpr h))

/-- 標準形の上で `cmp` が `.eq` ⟺ 等しい（仮定なし） -/
theorem cmp_eq_iff_NF (a b : NF) : cmp a.1 b.1 = .eq ↔ a = b := by
  constructor
  · intro e
    exact Subtype.ext (eqY a.2 b.2 e)
  · intro e
    rw [e]
    exact cmp_self _

/-- 標準形の上で `cmp` は反対称（仮定なし） -/
theorem cmp_swap_NF (a b : NF) : cmp b.1 a.1 = (cmp a.1 b.1).swap := swapY a.2 b.2

/-- 記法系の基本列（`Succ.lean` の `fs_psi_succ` と同じ主張を仮定なしで）：`Ψ_π(b+1)` が標準形で
    `π = Ω_0` か `Ω_{c'+1}` なら、`Ψ_π(b)·(n+1)`（`fsTerm`）は標準形で狭義増加し、`Ψ_π(b+1)` 未満で、
    `Ψ_π(b+1)` 未満の標準形はどれかの `Ψ_π(b)·(n+1)` 未満 -/
theorem fs_psi_succ_NF {pi c : Tm} (h : isNF (.Psi pi c) = true)
    (hpi : pi = .Om .zero ∨ ∃ c', pi = .Om c' ∧ isSucc c' = true) (hc : isSucc c = true) :
    isNF (.Psi pi (predT c)) = true ∧
      (∀ n, isNF (fsTerm pi (predT c) n) = true) ∧
      (∀ n, MahloOCF.lt (fsTerm pi (predT c) n) (fsTerm pi (predT c) (n + 1)) = true) ∧
      (∀ n, MahloOCF.lt (fsTerm pi (predT c) n) (.Psi pi c) = true) ∧
      (∀ x, isNF x = true → MahloOCF.lt x (.Psi pi c) = true →
        ∃ n, MahloOCF.lt x (fsTerm pi (predT c) n) = true) := by
  have toLt : ∀ {a b : Tm}, MahloOCF.lt a b = true ↔ Lt a b := by
    intro a b
    unfold MahloOCF.lt Lt
    simp only [beq_iff_eq]
  obtain ⟨h1, h2, h3, h4, h5⟩ := fs_psi_succY h hpi hc
  refine ⟨h1, h2, fun n => toLt.mpr (h3 n), fun n => toLt.mpr (h4 n), fun x hx hxt => ?_⟩
  obtain ⟨n, hn⟩ := h5 x hx (toLt.mp hxt)
  exact ⟨n, toLt.mpr hn⟩

/-! ### 大基数の仮定なしの順序数への値

上の整礎な狭義全順序から、標準形の値を順序型（始切片の型）で定める。値は `cmp` と一致し、値の集合は
記法系の順序型 `nfOrderType` 未満の順序数ちょうど。後続基数への崩壊の値は基本列の値の上限。
`Complete.lean` の `cmp_correct_of_isNF`・`nfValue_iff_C`、`Succ.lean` の `Psi_succ_fs` にあたる仮定なしの
形（値は弱 Mahlo 基数の上の崩壊関数ではなく、記法系自身の順序型による）。 -/

/-- 標準形全体の整列順序 -/
def nfWellOrder : WellOrder.{0} where
  Carrier := NF
  lt := NFLt
  irrefl := lt_strictTotal_NF.1
  trans := lt_strictTotal_NF.2.1
  total := lt_strictTotal_NF.2.2
  wellFounded := wellFounded_NFLt

/-- 標準形の値（始切片の順序型） -/
def ordVal (a : NF) : Ordinal.{0} := Ordinal.type (nfWellOrder.below a)

/-- 記法系の順序型 -/
def nfOrderType : Ordinal.{0} := Ordinal.type nfWellOrder

theorem ordVal_lt_iff (a b : NF) : ordVal a < ordVal b ↔ NFLt a b :=
  ⟨WellOrder.lt_of_below_below nfWellOrder a b, WellOrder.below_below_of_lt nfWellOrder a b⟩

theorem ordVal_inj {a b : NF} (h : ordVal a = ordVal b) : a = b := by
  cases Ordinal.iso_of_type_eq h with
  | intro e => exact WellOrder.eq_of_below_iso nfWellOrder a b e

/-- 値は記法系の順序型未満 -/
theorem ordVal_lt_type (a : NF) : ordVal a < nfOrderType := WellOrder.below_self nfWellOrder a

/-- 記法系の順序型未満の順序数は全てどれかの標準形の値 -/
theorem ordVal_surj {o : Ordinal.{0}} (h : o < nfOrderType) : ∃ a : NF, ordVal a = o := by
  obtain ⟨b, hb⟩ := (Ordinal.lt_type_iff o nfWellOrder).mp h
  exact ⟨b, hb.symm⟩

/-- 値の集合はちょうど `nfOrderType` 未満の順序数 -/
theorem ordVal_range (o : Ordinal.{0}) : (∃ a : NF, ordVal a = o) ↔ o < nfOrderType :=
  ⟨fun ⟨a, ha⟩ => ha ▸ ordVal_lt_type a, ordVal_surj⟩

/-- `cmp` は値の比較と一致する -/
theorem cmp_ordVal (a b : NF) :
    (cmp a.1 b.1 = .lt ↔ ordVal a < ordVal b) ∧ (cmp a.1 b.1 = .eq ↔ ordVal a = ordVal b) ∧
      (cmp a.1 b.1 = .gt ↔ ordVal b < ordVal a) := by
  have toNF : ∀ {x y : NF}, cmp x.1 y.1 = .lt ↔ NFLt x y := by
    intro x y
    unfold NFLt MahloOCF.lt
    simp only [beq_iff_eq]
  refine ⟨toNF.trans (ordVal_lt_iff a b).symm, (cmp_eq_iff_NF a b).trans
    ⟨fun e => by rw [e], ordVal_inj⟩, ?_⟩
  rw [ordVal_lt_iff b a, ← toNF, cmp_swap_NF a b]
  cases cmp a.1 b.1 <;> simp

/-- 後続基数への崩壊の値は基本列の値の上限（仮定なし） -/
theorem ordVal_fs {pi c : Tm} (h : isNF (.Psi pi c) = true)
    (hpi : pi = .Om .zero ∨ ∃ c', pi = .Om c' ∧ isSucc c' = true) (hc : isSucc c = true) :
    let t : NF := ⟨.Psi pi c, h⟩
    let s : Nat → NF := fun n => ⟨fsTerm pi (predT c) n, (fs_psi_succ_NF h hpi hc).2.1 n⟩
    (∀ n, ordVal (s n) < ordVal (s (n + 1))) ∧ (∀ n, ordVal (s n) < ordVal t) ∧
      (∀ o, o < ordVal t → ∃ n, o < ordVal (s n)) := by
  obtain ⟨-, -, h3, h4, h5⟩ := fs_psi_succ_NF h hpi hc
  refine ⟨fun n => (ordVal_lt_iff _ _).mpr (h3 n), fun n => (ordVal_lt_iff _ _).mpr (h4 n), ?_⟩
  intro o ho
  obtain ⟨x, rfl⟩ := ordVal_surj (Ordinal.lt_trans _ _ _ ho (ordVal_lt_type _))
  obtain ⟨n, hn⟩ := h5 x.1 x.2 ((ordVal_lt_iff x ⟨.Psi pi c, h⟩).mp ho)
  exact ⟨n, (ordVal_lt_iff x _).mpr hn⟩

end OCF.Mahlo

/-- info: 'OCF.Mahlo.wellFounded_NFLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.wellFounded_NFLt

/-- info: 'OCF.Mahlo.lt_strictTotal_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.lt_strictTotal_NF

/-- info: 'OCF.Mahlo.fs_psi_succ_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.fs_psi_succ_NF

/-- info: 'OCF.Mahlo.cmp_eq_iff_NF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.cmp_eq_iff_NF

/-- info: 'OCF.Mahlo.cmp_ordVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.cmp_ordVal

/-- info: 'OCF.Mahlo.ordVal_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_range

/-- info: 'OCF.Mahlo.ordVal_fs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OCF.Mahlo.ordVal_fs
