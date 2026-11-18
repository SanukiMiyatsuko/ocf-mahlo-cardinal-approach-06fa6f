import Mahlo.FS.Bach

/-! `BachHyp`（`ω` 型の Bachmann 性）の反例。今の基本列の定義では Bachmann 性は成り立たない。

外に足す型で `Ψ_σ(X) ≤ t` の対角化（`PsiFam.lean`）で、添字が `Ω` について閉じていない種 `c` の上の `Ω` の塔
`y_0 = Ω_{c+1}`、`y_1 = Ω_{Ω_{c+1}+1}`、… になる場合：

* `σ = Ξ_1(0)`、`P = Ψ_σ(M_1)`、`S1 = Ψ_{Ξ_1(σ+1)}(σ + P + 2)`、`X = S1 + σ`、`c = Ψ_{Ω_{P+1}}(5)`、
  `π = Ω_{c+1}`、`t = Ψ_π(X)`。`Ψ_σ(X)` は標準形でなく、`t` は `Ψ_σ(X)` 未満でない（`π` の底の条件を満たさない）。
* `t[n] = Ψ_π(S1 + y_n)`。`d = Ψ_{Ω_{P+1}}(ω)`（`c < d < Ω_{c+1}`、`d[0] = Ψ_{Ω_{P+1}}(2) < c`）について
  `b = Ψ_π(S1 + Ω_d)` は `t[0] < b < t[1] < t` だが、`b[0] = Ψ_π(S1 + Ω_{d[0]+1}) < t[0]`。

計算は `native_decide`（公理 `Lean.ofReduceBool` を使う）。`lake exe fstest probeBachCE2` でも同じ値を出力する。 -/

namespace MahloOCF.FS

open Tm

def ceSigma : Tm := Xi 1 zero
def ceP : Tm := Psi ceSigma (M 1)
def ceS1 : Tm := Psi (Xi 1 (plus ceSigma one)) (plus ceSigma (plus ceP (plus one one)))
def ceX : Tm := plus ceS1 ceSigma
def ceC : Tm := Psi (Om (sc ceP)) (ofNatT 5)
def cePi : Tm := Om (sc ceC)
def ceT : Tm := Psi cePi ceX
def ceD : Tm := Psi (Om (sc ceP)) (Psi (Om zero) one)
def ceB : Tm := Psi cePi (plus ceS1 (Om ceD))

def Cof.isOmega : Cof Tm → Bool
  | .omega => true
  | _ => false

theorem ce_dom : dom ceT = .omega := by
  have e : Cof.isOmega (dom ceT) = true := by native_decide
  revert e
  cases dom ceT <;> simp [Cof.isOmega]

theorem ce_t : WNF ceT := by unfold WNF; native_decide
theorem ce_b : WNF ceB := by unfold WNF; native_decide
theorem ce_lt1 : Lt (fundNat ceT 0) ceB := by unfold Lt; native_decide
theorem ce_lt2 : Lt ceB ceT := by unfold Lt; native_decide
theorem ce_not_le : ¬ Le (fundNat ceT 0) (fund ceB .zero) := by
  unfold Le Lt
  native_decide

/-- 今の基本列では `ω` 型の Bachmann 性は成り立たない -/
theorem not_bachHyp : ¬ BachHyp := fun h =>
  ce_not_le (h ceT ceB 0 ce_t ce_b ce_dom ce_lt1 ce_lt2)

end MahloOCF.FS
