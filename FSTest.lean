import Mahlo.FS.Seq

/-! 基本列の総当たりの検査：大きさ `S` 以下の標準形を全て作り、FS の各性質（標準形・減少・単調・共終・
Bachmann）を確かめる。 -/

open MahloOCF MahloOCF.FS Tm

/-- `isNF` をメモ化版の比較でコンパイルし直したもの -/
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

def maxM : Nat := 2

/-- 大きさ `s` の標準形（大きさ `s` 未満の表 `tbl` から作る） -/
def genSize (tbl : Array (Array Tm)) (s : Nat) : Array Tm := Id.run do
  let mut out : Array Tm := #[]
  if s == 1 then
    out := out.push zero
    for n in [1:maxM+1] do
      out := out.push (M n)
    return out
  -- Om a, Xi n a
  for a in tbl[s-1]! do
    let t := Om a
    if isNFF t then out := out.push t
    for n in [1:maxM+1] do
      let t := Xi n a
      if isNFF t then out := out.push t
  -- plus a b, Psi p a
  for i in [1:s-1] do
    let j := s - 1 - i
    if j ≥ 1 then
      for a in tbl[i]! do
        if isPrincipal a then
          for b in tbl[j]! do
            if b != zero then
              let t := plus a b
              if isNFF t then out := out.push t
      for p in tbl[i]! do
        if isRegTerm p then
          for a in tbl[j]! do
            let t := Psi p a
            if isNFF t then out := out.push t
  return out

def genAll (S : Nat) : Array Tm := Id.run do
  let mut tbl : Array (Array Tm) := #[#[]]
  for s in [1:S+1] do
    tbl := tbl.push (genSize tbl s)
  let mut all : Array Tm := #[]
  for a in tbl do
    all := all ++ a
  return all

def lt' (a b : Tm) : Bool := cmp a b == .lt
def le' (a b : Tm) : Bool := cmp a b != .gt

structure Stats where
  errs : Array String := #[]
  nOmega : Nat := 0
  nBig : Nat := 0
  nOne : Nat := 0

def addErr (st : Stats) (s : String) : Stats :=
  if st.errs.size < 400 then { st with errs := st.errs.push s } else st

/-- 昇順に並べた標準形 `all`（`x0` は各項の 0 番目）の中で、順位 `r` の項 `t` を調べる -/
def checkTerm (all x0 : Array Tm) (st0 : Stats) (r : Nat) (K : Nat) : Stats := Id.run do
  let mut st := st0
  let t := all[r]!
  let s := (info t).seq
  match s.dom with
  | .zero =>
    if t != zero then st := addErr st s!"dom zero but t ≠ 0: {repr t}"
  | .one =>
    st := { st with nOne := st.nOne + 1 }
    let p := fund t zero
    if !isNFF p then st := addErr st s!"succ pred not NF: {repr t} ↦ {repr p}"
    if !lt' p t then st := addErr st s!"succ pred not <: {repr t} ↦ {repr p}"
    if r > 0 && !le' all[r-1]! p then
      st := addErr st s!"succ cof: {repr t}, x = {repr all[r-1]!}, pred = {repr p}"
  | .omega =>
    st := { st with nOmega := st.nOmega + 1 }
    let seq := (List.range (K + 1)).toArray.map (fun n => fund t (ofNatT n))
    for n in [0:K+1] do
      let x := seq[n]!
      if !isNFF x then st := addErr st s!"ω not NF: {repr t} [{n}] = {repr x}"
      if !lt' x t then st := addErr st s!"ω not <: {repr t} [{n}] = {repr x}"
      if n < K && !lt' x seq[n+1]! then
        st := addErr st s!"ω not mono: {repr t} [{n}] = {repr x}, [{n+1}] = {repr seq[n+1]!}"
    -- 共終性（標本の中で t の直前の項が列の項以下か。足りなければ添字を伸ばす）
    if r > 0 then
      let x := all[r-1]!
      if !le' x seq[K]! then
        let ok := (List.range 40).any (fun n => le' x (fund t (ofNatT (n + K))))
        if !ok then st := addErr st s!"ω cof: {repr t}, x = {repr x}, [{K}] = {repr seq[K]!}"
    -- Bachmann：t[n] < b < t なら t[n] ≤ b[0]
    for n in [0:4] do
      let y := seq[n]!
      for i in [0:r] do
        let b := all[i]!
        if lt' y b then
          if !le' y x0[i]! then
            st := addErr st s!"Bachmann: {repr t} [{n}] = {repr y} < b = {repr b}, b[0] = {repr x0[i]!}"
  | .big σ =>
    st := { st with nBig := st.nBig + 1 }
    if !isNFF σ then st := addErr st s!"big σ not NF: {repr t}, σ = {repr σ}"
    let idx := all.filter (fun ξ => lt' ξ σ)
    let vals := idx.map (fun ξ => (ξ, fund t ξ))
    for (ξ, y) in vals do
      if !isNFF y then st := addErr st s!"big not NF: {repr t} [{repr ξ}] = {repr y}"
      if !lt' y t then st := addErr st s!"big not <: {repr t} [{repr ξ}] = {repr y}"
    for i in [1:vals.size] do
      if !lt' vals[i-1]!.2 vals[i]!.2 then
        st := addErr st s!"big not mono: {repr t} [{repr vals[i-1]!.1}] = {repr vals[i-1]!.2}, [{repr vals[i]!.1}] = {repr vals[i]!.2}"
    if r > 0 then
      let x := all[r-1]!
      let top := if vals.size > 0 then vals[vals.size-1]!.2 else zero
      if !le' x top then
        let ok := lt' x σ && le' x (fund t x)
        if !ok then st := addErr st s!"big cof (in sample): {repr t}, x = {repr x}, σ = {repr σ}"
  return st

/-- 挿入ソート風の併合ソート（`cmp` で昇順） -/
partial def msort (a : Array Tm) : Array Tm :=
  if a.size ≤ 1 then a
  else
    let m := a.size / 2
    let l := msort (a.extract 0 m)
    let r := msort (a.extract m a.size)
    Id.run do
      let mut out : Array Tm := #[]
      let mut i := 0
      let mut j := 0
      while i < l.size || j < r.size do
        if j ≥ r.size || (i < l.size && lt' l[i]! r[j]!) then
          out := out.push l[i]!
          i := i + 1
        else
          out := out.push r[j]!
          j := j + 1
      return out

/-! ### 手で選んだ種の項と、その基本列による閉包 -/

def nat' (n : Nat) : Tm := ofNatT n
def O (a : Tm) : Tm := Om a
def P (p a : Tm) : Tm := Psi p a
def add (a b : Tm) : Tm := oadd a b
def O0 : Tm := Om zero
def w : Tm := Psi O0 one
def e0 : Tm := Psi O0 O0
def M1 : Tm := M 1
def M2 : Tm := M 2
def M1p : Tm := succM 1
def X1 (a : Tm) : Tm := Xi 1 a
def X2 (a : Tm) : Tm := Xi 2 a

def seeds : List Tm :=
  let O1 := O one
  let O2 := O (nat' 2)
  let Ow := O w
  let OO := O O0
  [ nat' 3, w, add w one, add w w, O0, O1, O2, Ow, OO, O e0, O (add O0 one), O (add O0 w),
    e0, P O0 O1, P O0 Ow, P O0 OO, P O0 (add O0 one), P O0 (add O0 w), P O0 (add O0 O0), P O0 O2,
    P O1 zero, P O1 one, P O1 w, P O1 O0, P O1 O1, P O1 O2, P O1 (add O1 one), P O1 (add O1 O0),
    P O2 O2, P O0 (P O1 O1), P O0 (P O1 (P O2 O2)), P (O (nat' 2)) zero,
    M1, M2, M1p, add M1 M1, O (add M1 one), O (add M1 w), O (add M1 O0), O (add M1 M1),
    X1 zero, X1 one, X1 (nat' 2), X1 w, X1 O0, X1 O1, X1 (X1 zero), X1 M1, X1 (add M1 one),
    X1 (add M1 w), X1 (add M1 M1), X1 M1p, X1 (P M1p zero), X1 (P M1p one),
    P O0 M1, P O0 (X1 zero), P O0 M1p, P O0 (add M1p M1), P O0 (P M1p M1p), P O0 (add M1 one),
    P O0 (X1 M1p), P O1 M1, P O1 (X1 zero),
    P (X1 zero) one, P (X1 zero) (nat' 2), P (X1 zero) w, P (X1 zero) O0, P (X1 zero) O1,
    P (X1 zero) (X1 zero), P (X1 zero) M1, P (X1 zero) (add M1 one), P (X1 zero) M1p,
    P (X1 one) (nat' 2), P (X1 one) (nat' 3), P (X1 one) w, P (X1 (nat' 2)) (nat' 3),
    P (X1 w) (add w one), P (X1 w) (add w (nat' 2)), P (X1 w) (add w w), P (X1 w) O0,
    P (X1 O0) (add O0 one), P (X1 O0) (add O0 w), P (X1 O0) O1,
    P (X1 (X1 zero)) (add (X1 zero) one), P (X1 M1) (add M1 one), P (X1 M1) (add M1 w),
    P (X1 (add M1 one)) (add M1 (nat' 2)), P (X1 (add M1 one)) (add M1 (nat' 3)),
    P (X1 M1p) (add M1p one), P (X1 (add M1 M1)) (add (add M1 M1) one),
    P O0 (P (X1 zero) M1), P O0 (P (X1 (add M1 one)) (add M1 (nat' 2))),
    P (O (add (X1 zero) one)) zero, P (O (add (X1 zero) one)) (X1 zero), O (add (X1 zero) w),
    X2 zero, X2 M1, X2 M2, P (X2 zero) one, P O0 M2, P O0 (X2 zero), P (X2 M1) (add M1 one),
    P (X2 zero) M1, P (X1 zero) (P (X1 one) (nat' 2)) ]

/-- 部分項 -/
partial def subsT (t : Tm) : List Tm :=
  t :: (match t with
    | plus a b => subsT a ++ subsT b
    | Om a | Xi _ a => subsT a
    | Psi p a => subsT p ++ subsT a
    | _ => [])

/-- 基本列の項（`ω` 型は 0〜3 番目、`big` 型は小さい添字、後者は前者） -/
def children (small : Array Tm) (t : Tm) : List Tm :=
  match dom t with
  | .zero => []
  | .one => [fund t zero]
  | .omega => (List.range 4).map (fun n => fund t (ofNatT n))
  | .big σ => (small.filter (fun ξ => lt' ξ σ)).toList.map (fun ξ => fund t ξ)

def dedup (l : Array Tm) : Array Tm := Id.run do
  let mut seen : Std.HashMap Tm Unit := {}
  let mut out : Array Tm := #[]
  for t in l do
    if !seen.contains t then
      seen := seen.insert t ()
      out := out.push t
  return out

def seedSample (S0 D : Nat) : Array Tm := Id.run do
  let small := genAll S0
  let idxs : Array Tm := #[zero, one, nat' 2, w, O0, add O0 one, O (one), X1 zero, M1]
  let mut cur : Array Tm := (seeds.filter isNFF).toArray
  let mut acc : Array Tm := cur
  for _ in [0:D] do
    let mut nxt : Array Tm := #[]
    for t in cur do
      for c in children idxs t do
        nxt := nxt.push c
    nxt := dedup (nxt.filter isNFF)
    acc := acc ++ nxt
    cur := nxt
  let mut subs : Array Tm := #[]
  for t in acc do
    for s in subsT t do
      subs := subs.push s
  return dedup (small ++ acc ++ subs.filter isNFF)

/-- 計時：基本列の項 `t[n]` を `n` を増やしながら計算し、大きさと時間を表示する -/
def timing : IO Unit := do
  let ts : List (String × Tm) :=
    [("ε_0", e0), ("Ψ_Ω0(Ω_1)", P O0 (O one)), ("Ψ_Ω0(M_1)", P O0 M1),
     ("Ψ_Ω0(M_1^+)", P O0 M1p), ("Ψ_Ω0(Ψ_{Ξ1(M1+1)}(M1+2))", P O0 (P (X1 (add M1 one)) (add M1 (nat' 2)))),
     ("Ψ_Ω0(Ψ_{Ξ1(0)}(M_1))", P O0 (P (X1 zero) M1))]
  for (name, t) in ts do
    IO.println s!"{name}: isNF = {isNFF t}, dom = {match dom t with
      | .omega => "ω" | .big _ => "big" | .one => "1" | .zero => "0"}"
    -- 基本列を繰り返し下る（t, t[n], t[n][n], …）
    for n in [4, 8, 16, 32, 64] do
      let t0 ← IO.monoMsNow
      let x := fund t (ofNatT n)
      let sz := x.size
      let t1 ← IO.monoMsNow
      -- 降下列を 10 段たどる
      let mut y := x
      for _ in [0:10] do
        y := fund y (ofNatT n)
      let t2 ← IO.monoMsNow
      IO.println s!"  n = {n}: |t[n]| = {sz}, {t1 - t0} ms;  10 more steps: |y| = {y.size}, {t2 - t1} ms"

def main (args : List String) : IO Unit := do
  let mode := args.headD "6"
  if mode == "time" then
    timing
    return
  let K := 6
  let raw : Array Tm :=
    if mode == "seeds" then
      let S0 := (args[1]? >>= String.toNat?).getD 5
      let D := (args[2]? >>= String.toNat?).getD 2
      seedSample S0 D
    else genAll (mode.toNat?.getD 6)
  IO.println s!"non-NF seeds: {(seeds.filter (fun t => !isNFF t)).map repr}"
  let all := msort raw
  IO.println s!"terms: {all.size}"
  -- 並びが狭義単調であること（全順序の確認）
  for i in [1:all.size] do
    if !lt' all[i-1]! all[i]! then IO.println s!"order?: {repr all[i-1]!} {repr all[i]!}"
  let x0 := all.map (fun x => fund x zero)
  let mut st : Stats := {}
  for r in [0:all.size] do
    st := checkTerm all x0 st r K
  IO.println s!"one: {st.nOne}, omega: {st.nOmega}, big: {st.nBig}, errors: {st.errs.size}"
  for e in st.errs do
    IO.println e
