import Mahlo.FS.BachA2

/-! 基本列の最終結果：Bachmann 性（`bachHyp_proof`）と、標準形の型 `NF` 上の基本列の公理（`fsNF`、仮定なし）。

Bachmann 性は、崩壊以外の項と崩壊の各場合の `BInv`（Bachmann 性の強い形）から出る（`bachHyp_of_diag`）。
最後まで残っていた 3 つの場合は

* `M_m` への対角化（`psiDiagMBInv`、`BachDiagM.lean`）、
* `Ξ_m(q)` への崩壊の後者（族の閉包、`psiXiSuccBInv`、`BachFloor.lean`）、
* 外に足す型の対角化で族の閉包を添字にする場合（`psiDiagFamBInv`、`BachA2.lean`）。

最後の場合のために、族の閉包の種を `π` の前線の中で見える `Ψ_σ(·)` の最大のもの（`a2Seed`）に改めた
（以前の種（前線の最大元を `Ω` の塔に上げたもの）では、添字の区間 `(Ξ_k(H + Ω_{r+1}), …]` に
`Ξ_k(H + M_k + r)` の始点 `b`（`b[0] = Ξ_k(H + r)`）が入って Bachmann 性が壊れた）。 -/

namespace MahloOCF.FS

/-- Bachmann 性：`t[n] < b < t` なら `t[n] ≤ b[0]` -/
theorem bachHyp_proof : BachHyp := bachHyp_of_diag psiDiagFamBInv psiDiagMBInv psiXiSuccBInv

/-- 標準形の型 `NF` は基本列の公理（`ω` 型の Bachmann 性 `omega_bachmann` を含む）を満たす -/
@[reducible] def fsNF : FS NF := fsNFOf bachHyp_proof

end MahloOCF.FS

/-! `#print axioms` の出力を固定する検査。 -/

/-- info: 'MahloOCF.FS.bachHyp_proof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.bachHyp_proof

/-- info: 'MahloOCF.FS.fsNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MahloOCF.FS.fsNF
