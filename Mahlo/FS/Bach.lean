import Mahlo.FS.Inst

/-! Bachmann 性の言い換え：隣り合う列の項の区間の下界（梯子）。

`LBI x y`：区間 `(x, y]` の標準形 `b` は全て `x ≤ b[0]`。`LBI` は推移的なので（`LBI.trans`）、`ω` 型の項 `t` の
Bachmann 性は、全ての `n` で `LBI (t[n]) (t[n+1])` であることと、列の共終性から出る（`bachHyp_of_ladder`）。 -/

namespace MahloOCF.FS

open Tm

/-- 全ての標準形の列の性質 -/
theorem props_all (t : Tm) (ht : WNF t) : Props t := (inv_of t ht).props

/-- 区間 `(x, y]` の標準形 `b` は全て `x ≤ b[0]` -/
def LBI (x y : Tm) : Prop := ∀ b, WNF b → Lt x b → Le b y → Le x (fund b .zero)

theorem LBI.refl (x : Tm) (hx : WNF x) : LBI x x := fun _ hb hxb hbx =>
  absurd hxb (not_lt_of_leY hb hx hbx)

/-- `LBI` の推移性 -/
theorem LBI.trans {x y z : Tm} (hx : WNF x) (hy : WNF y) (hxy : Le x y) (h1 : LBI x y) (h2 : LBI y z) :
    LBI x z := by
  intro b hb hxb hbz
  rcases triY hb hy with h | e | h
  · exact h1 b hb hxb (Or.inr h)
  · exact h1 b hb hxb (Or.inl e)
  · exact le_transY hx hy (wnf_fund props_all hb WNF.zero) hxy (h2 b hb h hbz)

/-- 梯子：`ω` 型の項の隣り合う列の項の区間の下界 -/
def LadderHyp : Prop :=
  ∀ t n, WNF t → dom t = .omega → LBI (fundNat t n) (fundNat t (n + 1))

/-- 梯子から Bachmann 性 -/
theorem bachHyp_of_ladder (hL : LadderHyp) : BachHyp := by
  intro t b n ht hb hd h1 h2
  have hP := (props_all t ht).1 hd
  have hmono : ∀ i k, Le (fundNat t i) (fundNat t (i + k)) := by
    intro i k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ihk => exact le_transY (hP.nf i) (hP.nf _) (hP.nf _) ihk (Or.inr (hP.mono (i + k)))
  have chain : ∀ k, LBI (fundNat t n) (fundNat t (n + k)) := by
    intro k
    induction k with
    | zero => exact LBI.refl _ (hP.nf n)
    | succ k ih => exact LBI.trans (hP.nf n) (hP.nf _) (hmono n k) ih (hL t (n + k) ht hd)
  obtain ⟨m, hm⟩ := hP.cof b hb h2
  have hnm : n < m := by
    rcases Nat.lt_or_ge n m with hc | hc
    · exact hc
    exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
    exact not_lt_of_leY hb (hP.nf _) (le_transY hb (hP.nf m) (hP.nf _) hm (hmono m k)) h1
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact chain k b hb h1 hm

/-! ### 0 番目 -/

theorem wnf_f0 {t : Tm} (ht : WNF t) : WNF (fund t .zero) := wnf_fund props_all ht WNF.zero

/-- `0` でなければ `t[0] < t` -/
theorem f0_lt {t : Tm} (ht : WNF t) (h0 : t ≠ .zero) : Lt (fund t .zero) t := by
  have hP := props_all t ht
  cases hd : dom t with
  | zero => exact absurd ((dom_eq_zero_iff ht).mp hd) h0
  | one => rw [fund_of_dom_one _ hd]; exact pred_lt ht ((dom_eq_one_iff ht).mp hd)
  | omega => rw [fund_zero_omega hd]; exact (hP.1 hd).lt 0
  | big σ =>
    rw [fund_zero_big hd]
    have hB := hP.2 σ hd
    exact hB.lt _ WNF.zero hB.pos

theorem f0_le {t : Tm} (ht : WNF t) : Le (fund t .zero) t :=
  if h0 : t = .zero then by subst h0; exact Or.inl rfl else Or.inr (f0_lt ht h0)

theorem natProps_mono_le {t : Tm} (h : NatProps t) {i j : Nat} (hij : i ≤ j) :
    Le (fundNat t i) (fundNat t j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    exact le_transY (h.nf _) (h.nf _) (h.nf _) (ih (Nat.le_add_right _ _)) (Or.inr (h.mono (i + k)))

end MahloOCF.FS

/-- info: 'MahloOCF.FS.bachHyp_of_ladder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.bachHyp_of_ladder
