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

/-- 昇順の `all` で、`y < all[i]` となる最初の添字 -/
def upperIdx (all : Array Tm) (y : Tm) : Nat := Id.run do
  let mut lo := 0
  let mut hi := all.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if lt' y all[mid]! then hi := mid else lo := mid + 1
  return lo

/-- 昇順の `all` で、`y ≤ all[i]` となる最初の添字（`y` 未満の項の個数） -/
def lowerIdx (all : Array Tm) (y : Tm) : Nat := Id.run do
  let mut lo := 0
  let mut hi := all.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if lt' all[mid]! y then lo := mid + 1 else hi := mid
  return lo

/-- 部分項 -/
partial def subsT (t : Tm) : List Tm :=
  t :: (match t with
    | plus a b => subsT a ++ subsT b
    | Om a | Xi _ a => subsT a
    | Psi p a => subsT p ++ subsT a
    | _ => [])

/-- 昇順に並べた標準形 `all`（`x0` は各項の 0 番目）の中で、順位 `r` の項 `t` を調べる -/
def checkTerm (all x0 : Array Tm) (st0 : Stats) (r : Nat) (K : Nat) (B : Nat := 1000000) : Stats := Id.run do
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
      for i in [upperIdx all y:r] do
        let b := all[i]!
        if !le' y x0[i]! then
          st := addErr st s!"Bachmann: {repr t} [{n}] = {repr y} < b = {repr b}, b[0] = {repr x0[i]!}"
  | .big σ =>
    st := { st with nBig := st.nBig + 1 }
    if !isNFF σ then st := addErr st s!"big σ not NF: {repr t}, σ = {repr σ}"
    let cnt := lowerIdx all σ
    let stride := if cnt > B then cnt / B else 1
    let idx := Id.run do
      let mut o : Array Tm := #[]
      for i in [0:cnt] do
        if i % stride == 0 || i + 8 ≥ cnt then o := o.push all[i]!
      return o
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
        let cands := (subsT x).flatMap (fun u => [u, sc u])
        let ok := cands.any (fun ξ => lt' ξ σ && isNFF ξ && le' x (fund t ξ))
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

/-! ### かぶせた項：列の項 `u` に `Ω`・`Ξ`・`Ψ` をかぶせた項を標本に加える。

列 `t[n]` の上限と `t` の間に項が残っていないか（共終性の穴）を見つけるため。 -/

/-- `u` にかぶせた項（標準形とは限らない） -/
def wraps (u : Tm) : List Tm :=
  let su := sc u
  let tg := (((subsT u).filter isRegTerm) ++ [O0, O one, O su, X1 u, X2 u]).eraseDups
  [O u, O su, X1 u, X2 u, su, oadd u u] ++ tg.flatMap (fun ρ => [P ρ u, P ρ su, P ρ zero])

/-- `t = Ψ_π(X)` のすぐ下の項：`X` の最後の加数 `R` の列の項（とそれにかぶせた項）`w` の `Ψ_π(pre + w)` -/
def nearPreds (idxs : Array Tm) (t : Tm) : List Tm :=
  match t with
  | Psi π X =>
    match (summands X).getLast? with
    | none => []
    | some R =>
      let pre := ofSummands (summands X).dropLast
      (children idxs R).flatMap (fun c =>
        (c :: wraps c).filterMap (fun w =>
          if isNFF w && lt' w R then some (Psi π (oadd pre w)) else none))
  | _ => []

/-- 種の項とその列の項（深さ `D`）、それらにかぶせた項、崩壊のすぐ下の項 -/
def wrapSample (S0 D : Nat) : Array Tm := Id.run do
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
  acc := dedup (small ++ acc)
  let mut out : Array Tm := acc
  for t in acc do
    for v in wraps t do
      if isNFF v then out := out.push v
    for v in nearPreds idxs t do
      if isNFF v then
        out := out.push v
        for v2 in [X1 v, X2 v, O v, O (sc v)] do
          if isNFF v2 then out := out.push v2
  out := dedup out
  let mut subs : Array Tm := #[]
  for t in out do
    for s in subsT t do
      subs := subs.push s
  return dedup (out ++ subs.filter isNFF)

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

/-! ### 分岐の調査：各項の列の記述の形と、対角化の添字の計算で使われた分岐を数える -/

def cofLabel : Cof Tm → String
  | .zero => "0" | .one => "1" | .omega => "ω" | .big σ => match σ with
    | M _ => "M" | Om _ => "Ω" | Xi _ _ => "Ξ" | _ => "?"

def genLabel : Gen → String
  | .psi (Om _) => "ψΩ" | .psi (Xi _ _) => "ψΞ" | .psi _ => "ψ?" | .xi _ => "ξ"

partial def shapeLabel : SeqD → String
  | .none => "none" | .one => "one" | .reg _ _ _ => "reg" | .add _ s => s!"add({shapeLabel s})"
  | .iapp g _ r _ _ s => s!"iapp[{genLabel g},R:{cofLabel r.dom},idx:{shapeLabel s}]"
  | .om s => s!"om({shapeLabel s})" | .mul _ k => s!"mul{k}" | .tower _ => "tower"
  | .shift s => s!"shift({shapeLabel s})"
  | .app τ g pre R r P c =>
    let rd := r.dom
    let mode := match rd with
      | .big σ =>
        if ltB σ τ then "big<"
        else if canonK σ g pre R then "canonK"
        else if outsideMode τ σ g pre R then "outside"
        else "inside"
      | _ => "nat"
    s!"app[{genLabel g},R:{cofLabel rd},{mode},P{if P == zero then "0" else "+"},c{if c == zero then "0" else "+"}]"

/-- 対角化の添字の計算で使われた分岐（`col` の `virtK`・`base`、値の帰還） -/
def gamLabels (s : SeqD) (N : Nat) : List String := Id.run do
  match s with
  | .shift s' => return gamLabels s' N
  | .app τ g pre R r P c =>
    match r.dom with
    | .big σ =>
      if ltB σ τ then return []
      let mut out : List String := []
      let mut γ := gam τ σ g pre R r c P 0
      for k in [0:N] do
        if canonK σ g pre R then
          let δ := oadd (ofSummands pre) (r.big γ)
          match σ with
          | M m => if !leB δ (succM m) then out := "col:virtK" :: out
          | _ => pure ()
        else if outsideMode τ σ g pre R then
          let δ := match σ with
            | M _ => argOf τ σ g pre R r c P γ
            | _ => oadd (ofSummands pre) (r.big γ)
          match σ with
          | M m => if !leB δ (succM m) then out := "col:virtK(out)" :: out
          | _ => if !validR σ δ then out := "col:base(out)" :: out
        else
          let A := argOf τ σ g pre R r c P γ
          let cl := col σ A k
          match σ with
          | M m => if !leB A (succM m) then out := "col:virtK(in)" :: out
          | _ => if !validR σ A then out := "col:base(in)" :: out
          if ltB cl (g.ap A) && ltB (g.ap A) σ then out := "gam:return" :: out
        γ := gam τ σ g pre R r c P (k + 1)
      return out
    | _ => return []
  | _ => return []

def census (all : Array Tm) : IO Unit := do
  let mut cnt : Std.HashMap String (Nat × Tm) := {}
  for t in all do
    match t with
    | Psi π X =>
      let s := (info t).seq
      let base := if X == zero then "X=0" else if isSucc X then "succ" else "lim"
      let tgt := match π with | Om _ => "Ω" | Xi _ _ => "Ξ" | _ => "?"
      let lbl := s!"{tgt} {base}: {shapeLabel s}"
      cnt := cnt.insert lbl ((cnt.getD lbl (0, t)).1 + 1, (cnt.getD lbl (0, t)).2)
      for g in (gamLabels s 4).eraseDups do
        let l2 := s!"  {tgt} {base} {g}"
        cnt := cnt.insert l2 ((cnt.getD l2 (0, t)).1 + 1, (cnt.getD l2 (0, t)).2)
    | _ => pure ()
  let arr := cnt.toArray.qsort (fun a b => a.1 < b.1)
  for (l, (n, ex)) in arr do
    IO.println s!"{n}\t{l}\t e.g. {repr ex}"

/-! ### 大きな崩壊を目標に持つ項の局所的な検査（`lake exe fstest probe N`） -/

/-- 局所的な検査：標準形・元の項未満・単調（`ω` 型は `n = 0..N`、正則型はいくつかの添字） -/
def checkLocal (t : Tm) (N : Nat) (idxs : List Tm) : List String := Id.run do
  let mut errs : List String := []
  match dom t with
  | .omega =>
    for n in [0:N+1] do
      let a := fundNat t n
      let b := fundNat t (n + 1)
      if !isNFF a then errs := errs ++ [s!"notNF {repr t} [{n}] = {repr a}"]
      if !lt' a t then errs := errs ++ [s!"notLT {repr t} [{n}] = {repr a}"]
      if !lt' a b then errs := errs ++ [s!"notMONO {repr t} [{n}] = {repr a} vs [{n+1}] = {repr b}"]
  | .big σ =>
    let ix := idxs.filter (fun ξ => isNFF ξ && lt' ξ σ)
    for ξ in ix do
      let a := fundBig t ξ
      if !isNFF a then errs := errs ++ [s!"notNF {repr t} [{repr ξ}] = {repr a}"]
      if !lt' a t then errs := errs ++ [s!"notLT {repr t} [{repr ξ}] = {repr a}"]
    for ξ in ix do
      for η in ix do
        if lt' ξ η && !lt' (fundBig t ξ) (fundBig t η) then
          errs := errs ++ [s!"notMONO {repr t} [{repr ξ}] vs [{repr η}]"]
  | _ => pure ()
  return errs

/-- 正則項（崩壊先と `M`） -/
def probeRegs : List Tm :=
  [O0, O one, O (nat' 2), O (add w one), X1 zero, X1 one, X1 w, X1 M1, X1 (add M1 one), X1 (add M1 M1),
   X1 M1p, X1 (P M1p zero), X1 (add M1 (P M1p zero)), X1 (add M1 w),
   X1 (P M1p (O one)), X1 (add M1 (O one)), X1 (P M1p (X1 zero)),
   M1p, X2 zero, X2 M1, X2 M2, X2 (add M2 one), M1, M2]

/-- `M_m` の族について閉じた点（`Ξ_m(w)`、`w ≥ M_m`） -/
def probeClosed : List Tm :=
  [X1 M1, X1 (add M1 one), X1 (add M1 M1), X1 M1p, X2 M2, X2 (add M2 one)]

/-- 大きな崩壊 `Ψ_σ(w)`（`w ≥ σ` など） -/
def probeBigs : List Tm := Id.run do
  let mut out : List Tm := []
  for σ in probeRegs.filter isRegTerm do
    for a in [σ, add σ one, add σ (nat' 2), add σ σ, add σ w, O (add σ one), add M1 one, add M2 one, M1, M2,
        M1p, add M1p one, add (P M1p (O one)) σ, add (P M1p (O one)) one] do
      let k := P σ a
      if isNFF k then out := out ++ [k]
  return out

/-- 崩壊先の候補（大きな崩壊を含む） -/
def probePis : List Tm := Id.run do
  let mut out : List Tm := probeRegs.filter isRegTerm
  for k in probeBigs ++ probeClosed do
    for p in [O (sc k), O (sc (add k k)), X1 k, X1 (sc k), X2 k, X2 (sc k), X1 (add M1 k), X2 (add M2 k),
        O (sc (add k w))] do
      if isNFF p && isRegTerm p then out := out ++ [p]
  return out

/-- 引数の候補 -/
def probeArgs : List Tm := Id.run do
  let mut out : List Tm := []
  for σ in probeRegs do
    for a in [σ, add σ σ, add one σ, add w σ, O (add σ one), P O0 σ, add M1 σ, add (add M1 M1) σ,
        add M1p σ, add (P M1p zero) σ, add (P M1p (O one)) σ, add M2 σ] do
      if isNFF a then out := out ++ [a]
  for k in probeBigs do
    for a in [k, add k one, add k k, O (sc k), add k w] do
      if isNFF a then out := out ++ [a]
  return out ++ [one, nat' 2, w, add w one, M1, add M1 one, add M1 M1, M1p]

def probe (N : Nat) (stride : Nat) : IO Unit := do
  let idxs : List Tm := [zero, one, nat' 2, w, O0, add O0 one, O one, X1 zero, M1, add M1 one]
  let pis := probePis.toArray
  let args := probeArgs.toArray
  IO.println s!"pis: {pis.size}, args: {args.size}"
  let mut cnt := 0
  let mut nerr := 0
  let mut k := 0
  let mut kinds : Std.HashMap String (Nat × String) := {}
  for π in pis do
    for X in args do
      for X' in [X, sc X] do
        k := k + 1
        if k % stride == 0 then
          let t := P π X'
          if isNFF t then
            cnt := cnt + 1
            let es := checkLocal t N idxs
            nerr := nerr + es.length
            if !es.isEmpty then
              let base := if isSucc X' then "succ" else "lim"
              let tgt := match π with | Om _ => "Ω" | Xi _ _ => "Ξ" | _ => "?"
              let s := (info t).seq
              let lbl := s!"{tgt} {base}: {shapeLabel s} {(gamLabels s 4).eraseDups}"
              kinds := kinds.insert lbl ((kinds.getD lbl (0, es.headD "")).1 + 1,
                (kinds.getD lbl (0, es.headD "")).2)
  for (l, (n, ex)) in kinds.toArray do
    IO.println s!"{n}\t{l}\n\t{ex}"
  IO.println s!"probe: {cnt} terms, {nerr} errors"

/-- 外に足す型で `Ψ_σ(X) < t` の項の性質を調べる -/
def probeB (stride : Nat) : IO Unit := do
  let pis := probePis.toArray
  let args := probeArgs.toArray
  let mut cnt := 0
  let mut k := 0
  let mut stats : Std.HashMap String (Nat × String) := {}
  for π in pis do
    for X in args do
      k := k + 1
      if k % stride == 0 then
        let t := P π X
        if isNFF t && !isSucc X && X != zero then
          let xs := (info X).sums
          let pre := preT xs
          let R := lastT xs
          let r := lastS xs
          match r.dom with
          | .big (Xi m e) =>
            let σ := Xi m e
            let T := Psi σ (oadd (ofSummands pre) R)
            if !lt' σ π && outsideMode π σ (.psi π) pre R && lt' T t then
              cnt := cnt + 1
              let p := maxL (frB π π)
              let s := famSeq r.famOf σ p
              let s0 := s.first
              let note := fun (st : Std.HashMap String (Nat × String)) (lbl : String) (b : Bool) =>
                if b then st.insert lbl ((st.getD lbl (0, t.fmt)).1 + 1, (st.getD lbl (0, t.fmt)).2)
                else st
              stats := note stats "T NF" (isNFF T)
              stats := note stats "T not NF" (!isNFF T)
              stats := note stats "Base_σ(T)" (baseOf σ T)
              stats := note stats "not Base_σ(T)" (!baseOf σ T)
              stats := note stats "Base_σ(t)" (baseOf σ t)
              stats := note stats "e ∈ C(e, t)" (inC e e t)
              stats := note stats "π ∈ C(X, t)" (inC π X t)
              stats := note stats "p = none" (p.isNone)
              stats := note stats "p ≥ T" (match p with | some p => !lt' p T | none => false)
              stats := note stats "p < T" (match p with | some p => lt' p T | none => false)
              stats := note stats "t < s0" (lt' t s0)
              stats := note stats "s0 ≤ t" (!lt' t s0)
              stats := note stats "dom s = ω" (match s.dom with | .omega => true | _ => false)
              stats := note stats "dom s = big" (match s.dom with | .big _ => true | _ => false)
              stats := note stats "frσσ < T" ((frB σ σ).all (fun v => lt' v T))
              stats := note stats "frσσ ≥ T somewhere" (!(frB σ σ).all (fun v => lt' v T))
              stats := note stats "π lev = m" (lev π == m)
          | _ => pure ()
  for (l, (n, ex)) in stats.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"{n}\t{l}\t e.g. {ex}"
  IO.println s!"probeB: {cnt} terms"

/-- 不変量の検査：隙間（`t` の真の部分項で `t` 未満のものは列の項未満）・正則型の `ge`・`bge`・`lbK`・`lbS` -/
def checkInvs (t : Tm) (idxs : List Tm) : List String := Id.run do
  let mut errs : List String := []
  let sub := (subs t).filter (fun v => v != t && lt' v t)
  match dom t with
  | .omega =>
    for n in [0:3] do
      let a := fundNat t n
      for v in sub do
        if !lt' v a then errs := errs ++ [s!"gap {t.fmt} [{n}] = {a.fmt} ≤ sub {v.fmt}"]
  | .big σ =>
    let ix := idxs.filter (fun ξ => isNFF ξ && lt' ξ σ)
    for ξ in ix do
      let a := fundBig t ξ
      for v in sub do
        if lt' a v then errs := errs ++ [s!"gapBig {t.fmt} [{ξ.fmt}] = {a.fmt} < sub {v.fmt}"]
        if isPrincipal t && !lt' v a then errs := errs ++ [s!"gapP {t.fmt} [{ξ.fmt}] = {a.fmt} ≤ sub {v.fmt}"]
      if lt' a ξ then errs := errs ++ [s!"ge {t.fmt} [{ξ.fmt}] = {a.fmt}"]
      if lt' a (base σ) then errs := errs ++ [s!"bge {t.fmt} [{ξ.fmt}] = {a.fmt}"]
      match σ with
      | M m =>
        if lt' (M m) t && lt' a (M m) then errs := errs ++ [s!"lbK {t.fmt} [{ξ.fmt}]"]
        if lt' (succM m) t && lt' a (succM m) then errs := errs ++ [s!"lbS {t.fmt} [{ξ.fmt}]"]
      | _ => pure ()
  | _ => pure ()
  return errs

def probeInv (stride : Nat) : IO Unit := do
  let idxs : List Tm := [zero, one, nat' 2, w, O0, add O0 one, O one, X1 zero, M1, add M1 one]
  let pis := probePis.toArray
  let args := probeArgs.toArray
  let mut cnt := 0
  let mut nerr := 0
  let mut k := 0
  let mut kinds : Std.HashMap String (Nat × String) := {}
  for π in pis do
    for X in args do
      for X' in [X, sc X] do
        k := k + 1
        if k % stride == 0 then
          let t := P π X'
          if isNFF t then
            cnt := cnt + 1
            let es := checkInvs t idxs
            nerr := nerr + es.length
            if !es.isEmpty then
              let base := if isSucc X' then "succ" else "lim"
              let tgt := match π with | Om _ => "Ω" | Xi _ _ => "Ξ" | _ => "?"
              let lbl := s!"{tgt} {base}: {shapeLabel (info t).seq}"
              kinds := kinds.insert lbl ((kinds.getD lbl (0, es.headD "")).1 + 1,
                (kinds.getD lbl (0, es.headD "")).2)
  for (l, (n, ex)) in kinds.toArray do
    IO.println s!"{n}\t{l}\n\t{ex}"
  IO.println s!"probeInv: {cnt} terms, {nerr} errors"

/-! ### 族の閉包 `mahloVK` の分岐の調査（`lake exe fstest probeVK`） -/

def vkBranch (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) : String :=
  if q == zero then "B0:tower0"
  else if isSucc q then
    match splitPosD ceil qs.dropLast with
    | some _ => "B2:succApp"
    | none => "B1:succTower"
  else
    let s0 : SeqD := .app ceil (.xi m) (preT qs) (lastT qs) (lastS qs) zero zero
    match P with
    | none => "B3:s0"
    | some p =>
      if ltB p s0.first then "B4:s0"
      else if s0.first == p then "B5:shift"
      else match splitGtD p qs with
        | some _ => "B6:splitApp"
        | none => "B7:towerP"

/-- 族の候補 `Ξ_m(c)`：`q` の加数の先頭部分に小さな項や種を足したもの -/
def famCands (m : Nat) (q : Tm) (P : Option Tm) : List Tm := Id.run do
  let ss := summands q
  let extras : List Tm := [one, nat' 2, w, add w one] ++ (match P with | some p => [p, sc p, O (sc p)] | none => [])
  let mut out : List Tm := []
  for k in [0:ss.length + 1] do
    let L := ofSummands (ss.take k)
    for v in extras ++ ss.drop k do
      for c in [oadd L v, oadd L (sc v), oadd (oadd L v) v] do
        let z := Xi m c
        if isNFF z then out := out ++ [z, O (sc z)]
  return out

def probeVK (stride : Nat) : IO Unit := do
  let idxs : List Tm := [zero, one, nat' 2, w, O0, add O0 one, O one, X1 zero, M1, add M1 one]
  let pis := probePis.toArray
  let args := probeArgs.toArray
  let mut k := 0
  let mut stats : Std.HashMap String (Nat × String) := {}
  let mut nerr := 0
  for π in pis do
    for X in args do
      for X' in [X, sc X] do
        k := k + 1
        if k % stride == 0 then
          let t := P π X'
          if isNFF t then
            let note := fun (st : Std.HashMap String (Nat × String)) (lbl : String) =>
              st.insert lbl ((st.getD lbl (0, t.fmt)).1 + 1, (st.getD lbl (0, t.fmt)).2)
            -- 応用 1：`Ξ` 後者の残り
            match π with
            | Xi m q =>
              if isSucc X' then
                let Xp := pred X'
                let valid := lt' q Xp
                if !(valid && lt' q (M m)) then
                  let P : Option Tm := if valid then some (Psi π Xp) else maxL (frB π π)
                  let br := vkBranch m q (info q).sums π P
                  stats := note stats s!"A1 {if valid then "valid" else "floor"} {br}"
                  match P with
                  | some p =>
                    let tl := (summands q).dropWhile (fun u => lt' p u)
                    if !tl.isEmpty && !valid then
                      let lbl := s!"A1 floor {br} tail≠[]"
                      stats := note stats lbl
                      if (stats.getD lbl (0, "")).1 ≤ 3 then
                        IO.println s!"{lbl}: t = {t.fmt}\n   q = {q.fmt}, P = {p.fmt}, tail = {tl.map Tm.fmt}"
                  | none => pure ()
                  -- 共終性の検査（候補）
                  match dom t with
                  | .omega =>
                    let ys := (List.range 16).map (fundNat t)
                    for z in famCands m q P do
                      if lt' z t && !ys.any (fun y => lt' z y) then
                        nerr := nerr + 1
                        stats := note stats s!"A1 COF-FAIL {br}"
                        if nerr ≤ 5 then IO.println s!"A1 cof fail: t = {t.fmt}, z = {z.fmt}"
                  | _ => pure ()
              else pure ()
            | _ => pure ()
            -- 応用 2：外に足す型の対角化で `Ψ_σ(X) ≤ t`
            if !isSucc X' && X' != zero then
              let xs := (info X').sums
              let pre := preT xs
              let R := lastT xs
              let r := lastS xs
              match r.dom with
              | .big (Xi m e) =>
                let σ := Xi m e
                let T := Psi σ (oadd (ofSummands pre) R)
                if !lt' σ π && outsideMode π σ (.psi π) pre R && !lt' t T then
                  let P := maxL (frB π π)
                  let br := vkBranch m e (info e).sums σ P
                  stats := note stats s!"A2 {br}"
                  match P with
                  | some p =>
                    let tl := (summands e).dropWhile (fun u => lt' p u)
                    if !tl.isEmpty then
                      stats := note stats s!"A2 {br} tail≠[]"
                      if (stats.getD s!"A2 {br} tail≠[]" (0, "")).1 ≤ 3 then
                        IO.println s!"A2 {br} tail: t = {t.fmt}\n   e = {e.fmt}, P0 = {p.fmt}, tail = {tl.map Tm.fmt}"
                  | none => pure ()
                  let s := famSeq r.famOf σ P
                  if !isNFF T then stats := note stats "A2 T not NF !!"
                  if lev π != m then stats := note stats "A2 lev π ≠ lev σ !!"
                  for f in frB σ σ do
                    if !lt' f t then stats := note stats "A2 fr σ ≥ t !!"
                    if !lt' f T then stats := note stats "A2 fr σ ≥ T !!"
                  match P with
                  | some p =>
                    for u in summands e do
                      if lt' u σ && !lt' u T then stats := note stats "A2 e-summand<σ ≥ T !!"
                    if !(lt' T p || T == p) then stats := note stats "A2 P0 < T !!"
                  | none => stats := note stats "A2 P0 none (fr π empty)"
                  let s0 : SeqD := .app σ (.xi m) (preT (info e).sums) (lastT (info e).sums) (lastS (info e).sums) zero zero
                  match P with
                  | some p =>
                    if !lt' p t then stats := note stats "A2 P0 ≥ t !!"
                    if lt' p T then stats := note stats "A2 P0 < Ψσ(X)" else stats := note stats "A2 P0 ≥ Ψσ(X)"
                    if lt' p s0.first then stats := note stats "A2 P0 < s0.first" else stats := note stats "A2 P0 ≥ s0.first"
                  | none => stats := note stats "A2 P0 none"
                  -- 添字の共終性の検査（候補：`σ` 未満で `C(X, t)` に入るもの）
                  let ys : List Tm := match s.dom with
                    | .omega => (List.range 16).map s.nat
                    | .big τ => (idxs.filter (fun ξ => isNFF ξ && lt' ξ τ)).map s.big
                    | _ => []
                  for z in famCands m e P ++ [π, t, O (sc t)] do
                    if lt' z σ && inC z X' t && !ys.any (fun y => lt' z y) then
                      nerr := nerr + 1
                      stats := note stats s!"A2 HULL-FAIL {br}"
                      if nerr ≤ 5 then IO.println s!"A2 hull fail: t = {t.fmt}, z = {z.fmt}"
                else pure ()
              | _ => pure ()
  for (l, (n, ex)) in stats.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"{n}\t{l}\t e.g. {ex}"
  IO.println s!"probeVK: {nerr} failures"

/-- 底 `t = Ψ_{Ξ_m(q)}(q+1)` の調査：共終数・始点・隙間 -/
def probeFloor (stride : Nat) : IO Unit := do
  let pis := probePis.toArray
  let args := probeArgs.toArray
  let mut k := 0
  let mut stats : Std.HashMap String (Nat × String) := {}
  for π in pis do
    for X in args do
      for X' in [X, sc X] do
        k := k + 1
        if k % stride == 0 then
          let t := P π X'
          if isNFF t then
            let note := fun (st : Std.HashMap String (Nat × String)) (lbl : String) =>
              st.insert lbl ((st.getD lbl (0, t.fmt)).1 + 1, (st.getD lbl (0, t.fmt)).2)
            match π with
            | Xi m q =>
              if isSucc X' && !lt' q (pred X') then
                let P := maxL (frB π π)
                let br := vkBranch m q (info q).sums π P
                let y0 : Tm := match dom t with
                  | .big _ => fundBig t zero
                  | _ => fundNat t 0
                let dl := match dom t with
                  | .big σ => s!"big {σ.fmt}"
                  | .omega => "omega"
                  | _ => "other"
                stats := note stats s!"F {br} {if lt' q (M m) then "q<M" else "q≥M"} dom={match dom t with | .big _ => "big" | .omega => "ω" | _ => "?"}"
                match dom t with
                | .big σ =>
                  match P with
                  | some p => if lt' σ p then stats := note stats "F big σ<P0" else stats := note stats "F big σ≥P0 !!"
                  | none => stats := note stats "F big P0 none"
                  if !lt' (base σ) y0 then stats := note stats "F big base≥y0 !!"
                  let R := lastT (info q).sums
                  if br == "B4:s0" || br == "B3:s0" then
                    if lt' R (M m) then stats := note stats "F big s0 R<M" else stats := note stats s!"F big s0 R≥M ({dl})"
                | _ => pure ()
                match P with
                | some p => if !lt' p y0 then stats := note stats "F P0≥y0 !!"
                | none => pure ()
                -- 隙間
                for v in subs t do
                  if v != t && lt' v t && !lt' v y0 then
                    stats := note stats s!"F GAP-FAIL {br}"
                -- 部分項 `ρ` の真の部分項で `ρ` 未満のものと `y_0`
                for v in subs π do
                  if v != π && lt' v π && !lt' v y0 then
                    stats := note stats s!"F ρ-sub≥y0 {br}"
              else pure ()
            | _ => pure ()
  for (l, (n, ex)) in stats.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"{n}\t{l}\t e.g. {ex}"

/-- A2 の反例候補：`T = Ψ_σ(X)` が標準形でない場合 -/
def probeCE : IO Unit := do
  let σ : Tm := Xi 1 zero
  let P : Tm := Psi σ (M 1)
  let γ : Tm := plus σ (plus P (plus one one))
  let S1 : Tm := Psi (Xi 1 (plus σ one)) γ
  let X : Tm := plus S1 σ
  let π : Tm := Om (plus P one)
  let t : Tm := Psi π X
  let T : Tm := Psi σ X
  IO.println s!"NF: σ {isNFF σ}, P {isNFF P}, γ {isNFF γ}, S1 {isNFF S1}, X {isNFF X}, π {isNFF π}, t {isNFF t}, T {isNFF T}"
  IO.println s!"π < σ: {lt' π σ}, t < T: {lt' t T}, T < t: {lt' T t}"
  IO.println s!"dom σ: {match dom σ with | .big s => s.fmt | _ => "?"}"
  IO.println s!"dom t: {match dom t with | .big s => s!"big {s.fmt}" | .omega => "omega" | .one => "one" | .zero => "zero"}"
  for n in [0:4] do
    let y := fund t (ofNatT n)
    IO.println s!"t[{n}] = {y.fmt}  NF {isNFF y}  < t {lt' y t}"

/-- 梯子の検査：`ω` 型の `t` で、`t[n+1]` から 0 番目をたどる降下列が `t[n]` を飛び越えないか
（飛び越えれば Bachmann 性の反例：`t[n] < d ≤ t[n+1]` で `d[0] < t[n]`） -/
def probeLadder (stride : Nat) (maxN : Nat := 2) (lim : Nat := 300) : IO Unit := do
  let out ← IO.getStdout
  let pis := probePis.toArray
  let args := probeArgs.toArray
  let mut k := 0
  let mut cnt := 0
  let mut nerr := 0
  let mut nlim := 0
  let mut maxSteps := 0
  for π in pis do
    for X in args do
      for X' in [X, sc X] do
        k := k + 1
        if k % stride == 0 then
          let t := P π X'
          if isNFF t then
            match dom t with
            | .omega =>
              cnt := cnt + 1
              if cnt % 20 == 0 then
                out.putStrLn s!"... {cnt} ω-terms, {nerr} failures, {nlim} limits"
                out.flush
              for n in [0:maxN] do
                let x := fundNat t n
                let mut d := fundNat t (n + 1)
                let mut steps := 0
                let mut done := false
                while !done && steps < lim do
                  if !lt' x d then
                    done := true
                  else
                    let d0 := fund d zero
                    if lt' d0 x then
                      nerr := nerr + 1
                      if nerr ≤ 8 then
                        out.putStrLn s!"LADDER FAIL: t = {t.fmt}\n  t[{n}] = {x.fmt}\n  d = {d.fmt}\n  d[0] = {d0.fmt}"
                        out.flush
                      done := true
                    else
                      d := d0
                      steps := steps + 1
                if steps > maxSteps then maxSteps := steps
                if !done then nlim := nlim + 1
            | _ => pure ()
  out.putStrLn s!"probeLadder: {cnt} ω-terms, {nerr} failures, {nlim} step limits, max steps {maxSteps}"
  out.flush

/-- Bachmann 性の反例候補：種 `p`（`Ω` について閉じていない）の上の `Ω` の塔を添字にする外に足す型の対角化 -/
def probeBachCE : IO Unit := do
  let σ : Tm := X1 zero
  let B : Tm := P σ (sc zero)
  let ΩB1 : Tm := O (sc B)
  let p : Tm := P ΩB1 (nat' 5)
  let π : Tm := O (sc p)
  let t : Tm := P π σ
  IO.println s!"NF: σ {isNFF σ}, B {isNFF B}, p {isNFF p}, π {isNFF π}, t {isNFF t}"
  IO.println s!"base σ = B: {base σ == B}, P0 = {(maxL (frB π π)).map Tm.fmt}"
  IO.println s!"π < σ: {lt' π σ}, t < Ψ_σ(σ): {lt' t (P σ σ)}, B < t: {lt' B t}"
  IO.println s!"dom t: {match dom t with | .big s => s!"big {s.fmt}" | .omega => "omega" | .one => "one" | .zero => "zero"}"
  let t0 := fund t (nat' 0)
  let t1 := fund t (nat' 1)
  IO.println s!"t[0] = {t0.fmt}  NF {isNFF t0}\nt[1] = {t1.fmt}  NF {isNFF t1}"
  let d : Tm := P ΩB1 w
  let b : Tm := P π (O d)
  IO.println s!"d = {d.fmt} NF {isNFF d}, b = {b.fmt} NF {isNFF b}"
  IO.println s!"t[0] < b: {lt' t0 b}, b < t[1]: {lt' b t1}, b < t: {lt' b t}"
  let b0 := fund b zero
  IO.println s!"b[0] = {b0.fmt}  NF {isNFF b0}"
  IO.println s!"b[0] < t[0] (Bachmann violation): {lt' b0 t0}"

/-- Bachmann 性の反例候補 2：外に足す型で `Ψ_σ(X) ≤ t`（A2）、種 `c = Ψ_{Ω_{P+1}}(5)` の上の `Ω` の塔 -/
def probeBachCE2 : IO Unit := do
  let σ : Tm := Xi 1 zero
  let Pp : Tm := Psi σ (M 1)
  let γ : Tm := plus σ (plus Pp (plus one one))
  let S1 : Tm := Psi (Xi 1 (plus σ one)) γ
  let X : Tm := plus S1 σ
  let ΩP1 : Tm := O (sc Pp)
  let c : Tm := P ΩP1 (nat' 5)
  let π : Tm := O (sc c)
  let t : Tm := Psi π X
  let T : Tm := Psi σ X
  IO.println s!"NF: Pp {isNFF Pp}, S1 {isNFF S1}, X {isNFF X}, c {isNFF c}, π {isNFF π}, t {isNFF t}, T {isNFF T}"
  IO.println s!"P0 = {(maxL (frB π π)).map Tm.fmt}"
  IO.println s!"π < σ: {lt' π σ}, t < T: {lt' t T}, T < t: {lt' T t}"
  IO.println s!"dom t: {match dom t with | .big s => s!"big {s.fmt}" | .omega => "omega" | .one => "one" | .zero => "zero"}"
  let t0 := fund t (nat' 0)
  let t1 := fund t (nat' 1)
  IO.println s!"t[0] = {t0.fmt}  NF {isNFF t0}  < t {lt' t0 t}\nt[1] = {t1.fmt}  NF {isNFF t1}  < t {lt' t1 t}"
  let d : Tm := P ΩP1 w
  let b : Tm := Psi π (plus S1 (O d))
  IO.println s!"d = {d.fmt} NF {isNFF d}, b NF {isNFF b}"
  IO.println s!"t[0] < b: {lt' t0 b}, b < t[1]: {lt' b t1}, b < t: {lt' b t}"
  let b0 := fund b zero
  IO.println s!"b[0] = {b0.fmt}  NF {isNFF b0}"
  IO.println s!"b[0] < t[0] (Bachmann violation): {lt' b0 t0}"

def main (args : List String) : IO Unit := do
  let mode := args.headD "6"
  if mode == "probeBachCE" then
    probeBachCE
    return
  if mode == "probeBachCE2" then
    probeBachCE2
    return
  if mode == "probeLadder" then
    probeLadder ((args[1]? >>= String.toNat?).getD 1)
    return
  if mode == "probeCE" then
    probeCE
    return
  if mode == "probeFloor" then
    probeFloor ((args[1]? >>= String.toNat?).getD 1)
    return
  if mode == "probeVK" then
    probeVK ((args[1]? >>= String.toNat?).getD 1)
    return
  if mode == "probeInv" then
    probeInv ((args[1]? >>= String.toNat?).getD 1)
    return
  if mode == "probeB" then
    probeB ((args[1]? >>= String.toNat?).getD 1)
    return
  if mode == "time" then
    timing
    return
  if mode == "probe" then
    probe ((args[1]? >>= String.toNat?).getD 3) ((args[2]? >>= String.toNat?).getD 1)
    return
  if mode == "census" then
    let S0 := (args[1]? >>= String.toNat?).getD 7
    let all := dedup (genAll S0 ++ seedSample 5 2)
    IO.println s!"terms: {all.size}"
    census all
    return
  let K := 6
  let raw : Array Tm :=
    if mode == "seeds" then
      let S0 := (args[1]? >>= String.toNat?).getD 5
      let D := (args[2]? >>= String.toNat?).getD 2
      seedSample S0 D
    else if mode == "wrap" then
      let S0 := (args[1]? >>= String.toNat?).getD 4
      let D := (args[2]? >>= String.toNat?).getD 1
      wrapSample S0 D
    else genAll (mode.toNat?.getD 6)
  let B : Nat := if mode == "wrap" then 60 else 1000000
  IO.println s!"non-NF seeds: {(seeds.filter (fun t => !isNFF t)).map repr}"
  let all := msort raw
  IO.println s!"terms: {all.size}"
  -- 並びが狭義単調であること（全順序の確認）
  for i in [1:all.size] do
    if !lt' all[i-1]! all[i]! then IO.println s!"order?: {repr all[i-1]!} {repr all[i]!}"
  let x0 := all.map (fun x => fund x zero)
  let mut st : Stats := {}
  for r in [0:all.size] do
    st := checkTerm all x0 st r K B
  IO.println s!"one: {st.nOne}, omega: {st.nOmega}, big: {st.nBig}, errors: {st.errs.size}"
  for e in st.errs do
    IO.println e
