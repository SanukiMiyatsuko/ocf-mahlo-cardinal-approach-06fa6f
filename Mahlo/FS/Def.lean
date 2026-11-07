import Mahlo.FS.Memo
import Mahlo.WF.Syntax

/-! 基本列の定義に使う補助の関数（和・自然な和・正則項の列の始点・前線など）。
基本列そのものは `Mahlo.FS.Seq` で定義する。比較 `cmp` は使うが、項の総当たりはしない。
`Mahlo.FS.Memo` を読み込むので、ここから先のコードでは `cmp`・`inC` はメモ化版で計算される。 -/

namespace MahloOCF.FS

open Tm

def ltB (a b : Tm) : Bool := cmp a b == .lt
def leB (a b : Tm) : Bool := cmp a b != .gt

/-- 加数の列の併合（大きい順） -/
def merge : List Tm → List Tm → List Tm
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if leB y x then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- 自然な和 -/
def nsum (x y : Tm) : Tm := ofSummands (merge (summands x) (summands y))

/-- 順序数の和 -/
def oadd (x y : Tm) : Tm :=
  match summands y with
  | [] => x
  | h :: _ => ofSummands (((summands x).takeWhile (fun s => leB h s)) ++ summands y)

def mulNat (x : Tm) (n : Nat) : Tm := ofSummands (List.replicate n x)

/-- 自然数の項 `1 + ⋯ + 1` なら個数、そうでなければ `0` -/
def natOf (ξ : Tm) : Nat := if (summands ξ).all (· == one) then (summands ξ).length else 0

def ofNatT (n : Nat) : Tm := mulNat one n

/-- 最後の加数を除く -/
def pred (a : Tm) : Tm := ofSummands (summands a).dropLast

/-- `a + 1` -/
def sc (a : Tm) : Tm := succT a

/-- 正則項の列の始点：`Ω_0 ↦ 0`、`Ω_{c+1} ↦ Ω_c`、`M_n ↦ M_{n-1}`、`Ξ_n(d) ↦ Ψ_{Ξ_n(d)}(d+1)` -/
def base (σ : Tm) : Tm :=
  match σ with
  | Om c => if c = zero then zero else omOf (pred c)
  | M n => kTerm (n - 1)
  | Xi n d => Psi (Xi n d) (sc d)
  | _ => zero

/-- 階 `n` の下端 `M_{n-1}` -/
def floorLev (n : Nat) : Tm := kTerm (n - 1)

/-- 目標の引数の下限（`Ξ_n(d)` なら `d`） -/
def argR? (π : Tm) : Option Tm :=
  match π with
  | Xi _ d => some d
  | _ => none

/-- `Ψ_π(δ)` の引数の下限を満たすか -/
def validR (π δ : Tm) : Bool :=
  match argR? π with
  | some r => ltB r δ
  | none => true

/-- 前線（`Bool` 版） -/
def frB (R : Tm) : Tm → List Tm
  | plus a b => frB R a ++ frB R b
  | Om a => frB R a
  | Xi m a => if ltB (Xi m a) R then [Xi m a] else frB R a
  | Psi p a => if ltB (Psi p a) R then [Psi p a] else frB R p ++ frB R a
  | _ => []

def maxL : List Tm → Option Tm
  | [] => none
  | x :: xs =>
    match maxL xs with
    | none => some x
    | some y => if ltB x y then some y else some x

def maxO (P : Option Tm) (x : Tm) : Tm :=
  match P with
  | none => x
  | some p => if ltB p x then x else p

def maxOpt (P Q : Option Tm) : Option Tm :=
  match P, Q with
  | none, q => q
  | p, none => p
  | some p, some q => some (if ltB p q then q else p)

/-- `r` が `pre` で始まるなら、`r` の残り -/
def tailRaw (r? : Option Tm) (pre : List Tm) : Option Tm :=
  match r? with
  | none => none
  | some r =>
    if pre.length ≤ (summands r).length ∧ (summands r).take pre.length = pre
    then some (ofSummands ((summands r).drop pre.length)) else none

/-- `G` から始まる `Ω` の塔 -/
def tower (G : Tm) : Nat → Tm
  | 0 => G
  | k + 1 => Om (sc (tower G k))

/-- `M_m` への仮想的な崩壊 `κ_m(M_m⁺ + 1)` の列の正準な塔：`g_0 = 0`、`g_{k+1} = Ψ_{M_m⁺}(ψ₀ ⊕ g_k)`
    （`ψ₀ = Ψ_{M_m⁺}(0)`） -/
def virtG (m : Nat) : Nat → Tm
  | 0 => zero
  | k + 1 => Psi (succM m) (oadd (Psi (succM m) zero) (virtG m k))

/-- `κ_m(M_m⁺ + 1)` の列：`Ξ_m((ψ₀ ⊕ g_k) # Ξ_m(M_m⁺))` -/
def virtK (m k : Nat) : Tm :=
  Xi m (nsum (oadd (Psi (succM m) zero) (virtG m k)) (Xi m (succM m)))

end MahloOCF.FS
