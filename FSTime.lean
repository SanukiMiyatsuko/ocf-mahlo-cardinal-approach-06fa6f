import Mahlo.FS.Seq

/-! 計時：基本列の項 `t[n]` を `n` を増やしながら計算し、項の大きさと時間を表示する。 -/

open MahloOCF MahloOCF.FS Tm

def isNFF (t : Tm) : Bool :=
  match t with
  | zero => true
  | M n => n ≥ 1
  | plus a b =>
    isPrincipal a && b != zero && isNFF a && isNFF b &&
      (match summands b with
       | h :: _ => cmp h a != .gt
       | [] => false)
  | Om a => isNFF a && !(omegaFixed a)
  | Xi n a => n ≥ 1 && isNFF a && cmp a (succM n) != .gt && inC a a (M n)
  | Psi pi a =>
    isNFF pi && isNFF a && isRegTerm pi &&
      (match pi with
       | Xi _ d => cmp d a == .lt
       | _ => true) &&
      inC a a (Psi pi a)

def nat' (n : Nat) : Tm := ofNatT n
def O0 : Tm := Om zero
def M1 : Tm := M 1
def X1 (a : Tm) : Tm := Xi 1 a

def main : IO Unit := do
  let ts : List (String × Tm) :=
    [("ε_0", Psi O0 O0), ("Ψ_Ω0(Ω_1)", Psi O0 (Om one)), ("Ψ_Ω0(M_1)", Psi O0 M1),
     ("Ψ_Ω0(M_1^+)", Psi O0 (succM 1)),
     ("Ψ_Ω0(Ψ_{Ξ1(M1+1)}(M1+2))", Psi O0 (Psi (X1 (oadd M1 one)) (oadd M1 (nat' 2)))),
     ("Ψ_Ω0(Ψ_{Ξ1(0)}(M_1))", Psi O0 (Psi (X1 zero) M1))]
  for (name, t) in ts do
    IO.println s!"{name}: isNF = {isNFF t}"
    for n in [1, 2, 4, 8, 16, 32, 64, 128] do
      let t0 ← IO.monoMsNow
      let x := fund t (ofNatT n)
      let sz := x.size
      let t1 ← IO.monoMsNow
      IO.println s!"  n = {n}: |t[n]| = {sz}, {t1 - t0} ms"
      (← IO.getStdout).flush
    -- 降下列 t, t[2], t[2][2], …
    let mut y := t
    for k in [0:12] do
      let t0 ← IO.monoMsNow
      y := fund y (ofNatT 2)
      let t1 ← IO.monoMsNow
      IO.println s!"  step {k+1}: |y| = {y.size}, {t1 - t0} ms"
      (← IO.getStdout).flush
