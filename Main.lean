import Mahlo

open MahloOCF Tm

/-- いくつかの標準形 -/
def examples : List (String × Tm) :=
  let O0 := Om zero
  [("1", one), ("ω", Psi O0 one), ("ε_0", Psi O0 O0), ("ε_0·ω", Psi O0 (plus O0 one)),
   ("Ω_0", O0), ("Ω_1", Om one), ("Ξ_1(0)", Xi 1 zero), ("Ψ_{Ξ_1(0)}(1)", Psi (Xi 1 zero) one),
   ("Ξ_1(1)", Xi 1 one), ("M_1", M 1), ("M_1^+", succM 1), ("Ψ_{Ω_0}(M_1)", Psi O0 (M 1))]

def main : IO Unit := do
  for (name, t) in examples do
    IO.println s!"{name}: {repr t}  isNF = {isNF t}"
  IO.println s!"Ψ_Ω0(ε_0+1) は標準形でない: isNF = {isNF (Psi (Om zero) (plus (Psi (Om zero) (Om zero)) one))}"
  IO.println s!"Ξ_1(M_1^+ + 1) は引数の上限 M_1^+ を超えるので標準形でない: isNF = {isNF (Xi 1 (plus (succM 1) one))}"
