import Mahlo.Unconditional

/-! 二つの意味論の一致。

* 意味論 1（`Setting.lean` 以降）：弱 Mahlo 基数の増加列 `M_1 < M_2 < ⋯`（`Setting`。崩壊関数 `Ψ`・`Ξ` は
  この列の上で定義される）の上の崩壊関数による値 `val`。
* 意味論 2（`Unconditional.lean`）：記法系の整礎な狭義全順序の始切片の順序型による値 `ordVal`
  （仮定なし）。

どの `Setting` についても、標準形の値の順序は二つの意味論で一致し、崩壊関数の閉包 `C(Λ, 0)`（標準形の値の
集合）は順序を保って `nfOrderType` 未満の順序数と一対一に対応する。 -/

namespace OCF.Mahlo

universe u

open Ordinal MahloOCF

/-- `Setting` の中身：弱 Mahlo 基数の狭義増加列そのもの（崩壊関数の定義に使うデータ） -/
theorem setting_iff :
    Nonempty Setting.{u} ↔
      ∃ M : Nat → Ordinal.{u}, (∀ n, WeaklyMahlo (M n)) ∧ (∀ n, M n < M (n + 1)) :=
  ⟨fun ⟨s⟩ => ⟨s.Kseq, s.Kseq_mahlo, s.Kseq_lt⟩,
    fun ⟨M, hM, hlt⟩ => ⟨⟨M, hM, hlt⟩⟩⟩

variable [Setting.{u}]

/-- 二つの意味論で標準形の値の順序は一致する -/
theorem val_lt_iff_ordVal_lt (a b : NF) : val.{u} a.1 < val b.1 ↔ ordVal a < ordVal b :=
  (lt_iff_val a.2 b.2).symm.trans (ordVal_lt_iff a b).symm

/-- 二つの意味論で標準形の値の相等は一致する -/
theorem val_eq_iff_ordVal_eq (a b : NF) : val.{u} a.1 = val b.1 ↔ ordVal a = ordVal b :=
  ⟨fun e => by rw [Subtype.ext (val_inj_of_isNF a.2 b.2 e)],
    fun e => by rw [ordVal_inj e]⟩

/-- 崩壊関数の閉包 `C(Λ, 0)` は、値 `val` と `ordVal` を通して `nfOrderType` 未満の順序数と順序を保って
    一対一に対応する：`C(Λ, 0)` の元はどれかの標準形の値で、`val` と `ordVal` は同じ順序を与え、
    `ordVal` の値はちょうど `nfOrderType` 未満の順序数 -/
theorem closure_iso_orderType :
    (∀ x, C Λ 0 x ↔ ∃ a : NF, val.{u} a.1 = x) ∧
      (∀ a b : NF, val.{u} a.1 < val b.1 ↔ ordVal a < ordVal b) ∧
      (∀ a b : NF, val.{u} a.1 = val b.1 ↔ a = b) ∧
      (∀ o, (∃ a : NF, ordVal a = o) ↔ o < nfOrderType) := by
  refine ⟨fun x => ?_, val_lt_iff_ordVal_lt, fun a b => ?_, ordVal_range⟩
  · rw [← nfValue_iff_C]
    exact ⟨fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e⟩, fun ⟨a, e⟩ => ⟨a.1, a.2, e⟩⟩
  · exact ⟨fun e => Subtype.ext (val_inj_of_isNF a.2 b.2 e), fun e => by rw [e]⟩

end OCF.Mahlo
