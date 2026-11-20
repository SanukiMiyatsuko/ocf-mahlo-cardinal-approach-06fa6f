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


def lt' (a b : Tm) : Bool := cmp a b == .lt
def le' (a b : Tm) : Bool := cmp a b != .gt

partial def subsT (t : Tm) : List Tm :=
  t :: (match t with
    | plus a b => subsT a ++ subsT b
    | Om a | Xi _ a => subsT a
    | Psi p a => subsT p ++ subsT a
    | _ => [])

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

def dedup (l : Array Tm) : Array Tm := Id.run do
  let mut seen : Std.HashMap Tm Unit := {}
  let mut out : Array Tm := #[]
  for t in l do
    if !seen.contains t then
      seen := seen.insert t ()
      out := out.push t
  return out

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

def dedupL (l : List Tm) : List Tm := (dedup l.toArray).toList

/-- Bachmann 性の候補 `b`：部分項・降下列・`Ω`・`Ξ`・崩壊の引数の差し替え（`ω` 系の「悪い点」を混ぜる） -/
def bachCands (t x y : Tm) : List Tm := Id.run do
  let base := dedupL (subsT t ++ subsT x ++ subsT y)
  let mut extra : List Tm := [one, nat' 2, w, add w one, O0]
  for u in base do
    match u with
    | Psi (Om c) a =>
      if c != zero then extra := extra ++ [Psi (Om c) w, Psi (Om c) (add a w), Psi (Om c) (sc a)]
    | _ => pure ()
  let pool0 := dedupL (base ++ extra)
  let pool := dedupL (pool0 ++ pool0.map (fun d => Om d) ++ pool0.map (fun d => Om (sc d)))
  let mut out : List Tm := []
  let mut dd := y
  for _ in [0:40] do
    out := dd :: out
    dd := fund dd zero
  for d in pool do
    out := Om d :: Xi 1 d :: out
  for z in [x, y] do
    match z with
    | Psi π A =>
      let pre := ofSummands (summands A).dropLast
      for d in pool do
        out := Psi π (oadd A d) :: Psi π (oadd pre d) :: out
    | _ => pure ()
  return out

def chainL (y : Tm) (B : Nat) : List Tm := Id.run do
  let mut out : List Tm := []
  let mut z := y
  for _ in [0:B] do
    out := out ++ [z]
    if z == zero then return out
    z := fund z zero
  return out

set_option maxHeartbeats 2000000 in
/-- 底（`Ψ_{Ξ_m(q)}(q+1)`）の種つきの近似：種の閉性と区間の評価の調査 -/
def probeFloorSeed (maxN : Nat := 2) : IO Unit := do
  let out ← IO.getStdout
  -- `q` の候補：`R + p`（`R ≥ M_1`、`p` は節点）
  let highs : List Tm := [P M1p zero, P M1p one, P M1p w, P M1p (O one), add (P M1p zero) (P M1p zero),
    P M1p M1, P M1p (add M1 one), M1, add M1 M1]
  let nodes : List Tm := [X1 M1p, X1 (add M1p one), X1 (P M1p zero), X1 (add (P M1p zero) one),
    X1 (add M1 one), X1 M1, P (X1 M1p) (add M1p one), P (X1 (P M1p zero)) (add (P M1p zero) one),
    X1 (add (P M1p one) one), X1 (P M1p w), P (X1 M1p) (add M1p (nat' 2)), X1 (add M1p M1)]
  let mut qs : List Tm := []
  for h in highs do
    for p in nodes do
      qs := qs ++ [add h p, add h (add p p), add (add h h) p]
      for p2 in nodes do
        qs := qs ++ [add h (O (sc p2))]
  for a in probeArgs do
    qs := qs ++ [a]
  for p in nodes do
    qs := qs ++ [P M1p p, P M1p (add p one), P M1p (add M1 p), add (P M1p zero) (P M1p p), P M1p (O (sc p)),
      P M1p (add p p), add M1 (P M1p p)]
  let mut nfound := 0
  let mut nviol := 0
  let mut nbad := 0
  let mut nchk := 0
  let mut nprint := 0
  for q in qs do
    let ρ := X1 q
    if isNFF ρ then
      let t := P ρ (sc q)
      if isNFF t then
        match (info t).seq with
        | .app _ _ pre R r P' _ =>
          let isDiag := match r.dom with
            | .big σ => !lt' σ ρ
            | _ => false
          let isOm := match r.dom with
            | .omega => true
            | _ => false
          if P' != zero && !isDiag then
            nfound := nfound + 1
            if nprint < 8 then
              nprint := nprint + 1
              out.putStrLn s!"FLOOR-SEEDED: q = {q.fmt}\n  seed = {P'.fmt}  R = {R.fmt}  pre = {pre.length}"
            let caseB := (summands q).getLast? == some R
            if caseB then
              out.putStrLn s!"CASE-B: q = {q.fmt}  seed = {P'.fmt}  isOm = {isOm}"
            let xs : List Tm := if isOm then (List.range maxN).map (fun n => fundNat R n)
              else [fundBig R zero, fundBig R one, fundBig R w, fundBig R O0]
            for x in xs do
              let H := oadd (ofSummands pre) x
              for f in frB (M 1) H do
                if !lt' f P' then
                  out.putStrLn s!"FRONT-VIOL: q = {q.fmt}  x = {x.fmt}  f = {f.fmt}"
            for n in [0:maxN] do
              let H := oadd (ofSummands pre) (fundNat R n)
              let y := Xi 1 (oadd H P')
              let y' := fundNat t (n + 1)
              -- 閉性：`c < P'` の `Ξ_1(H + c)` は `P'` 未満か
              let cands := dedupL (subsT t ++ chainL P' 12 ++ [one, w, O0, M1, P M1p zero])
              for c0 in cands do
                for c in [c0, O (sc c0), add c0 one] do
                  if lt' c P' && isNFF (Xi 1 (oadd H c)) then
                    nchk := nchk + 1
                    if !lt' (Xi 1 (oadd H c)) P' then
                      nviol := nviol + 1
                      if nviol < 6 then
                        out.putStrLn s!"CLOSED-VIOL: q = {q.fmt}\n  H = {H.fmt}\n  c = {c.fmt}"
              -- 区間の評価
              for b in bachCands t y y' do
                if isNFF b && lt' y b && le' b y' then
                  if !le' y (fund b zero) then
                    nbad := nbad + 1
                    if nbad < 6 then
                      out.putStrLn s!"BACH-FAIL: q = {q.fmt} n = {n}\n  b = {b.fmt}\n  b[0] = {(fund b zero).fmt}"
        | _ => pure ()
  out.putStrLn s!"probeFloorSeed: found {nfound}, closedness checks {nchk}, violations {nviol}, bach failures {nbad}"
  out.flush



/-- 項の高い部分（`M_1` 以上の加数） -/
def hiPart (A : Tm) : Tm := ofSummands ((summands A).filter (fun u => !lt' u M1))

/-- A2 の検査を 1 つの `t` について行う -/
def checkA2 (out : IO.FS.Stream) (t : Tm) (stats : Array Nat) : IO (Array Nat) := do
  let mut st := stats
  match (info t).seq with
  | .iapp g pre r P c s =>
    st := st.modify 0 (· + 1)
    let π := match t with
      | Psi p _ => p
      | _ => zero
    let seed := match s with
      | .app _ _ _ _ _ P' _ => P'
      | .tower G => G
      | _ => zero
    let isOm := match s.dom with
      | .omega => true
      | _ => false
    if isOm then
      -- 共終性の目安：π < y_n
      let mut cof := false
      for n in [0:6] do
        if lt' π (s.nat n) then cof := true
      if !cof then
        st := st.modify 1 (· + 1)
        if st[1]! < 4 then out.putStrLn s!"NOCOF: t = {t.fmt}\n  seed = {seed.fmt}"
      for n in [0:3] do
        let tn := fundNat t n
        let tn' := fundNat t (n + 1)
        if !(isNFF tn && lt' tn t && lt' tn tn') then
          st := st.modify 2 (· + 1)
          if st[2]! < 4 then out.putStrLn s!"BAD-SEQ: t = {t.fmt} n = {n}\n  t[n] = {tn.fmt}"
      for n in [0:2] do
        let y := s.nat n
        let y' := s.nat (n + 1)
        let A := match y with
          | Xi _ a => a
          | _ => zero
        let H := hiPart A
        let roots := (subsT seed).filter (fun u => omegaFixed u && le' u seed)
        let mut cands : List Tm := []
        for rt in roots ++ [seed] do
          cands := cands ++ [Xi 1 (oadd H (oadd M1 rt)), Xi 1 (oadd H (oadd M1 (sc rt))),
            Xi 1 (oadd H rt), Xi 1 (oadd H (oadd M1 M1)), Xi 1 (oadd (oadd H M1) rt)]
        let cands2 := cands ++ cands.map (fun b => match b with
          | Xi n E => Psi (Xi n E) (sc E)
          | _ => b)
        for b in cands2 ++ bachCands t y y' do
          if isNFF b && lt' y b && le' b y' && !le' y (fund b zero) then
            st := st.modify 3 (· + 1)
            if st[3]! < 4 then
              out.putStrLn s!"IDX-FAIL: t = {t.fmt}\n  y = {y.fmt}\n  b = {b.fmt}\n  b[0] = {(fund b zero).fmt}"
          let bt := g.ap (combine g pre c P (r.big b))
          let tn := fundNat t n
          let tn' := fundNat t (n + 1)
          if isNFF b && isNFF bt && lt' tn bt && le' bt tn' && !le' tn (fund bt zero) then
            st := st.modify 4 (· + 1)
            if st[4]! < 4 then
              out.putStrLn s!"T-FAIL(lift): t = {t.fmt}\n  bt = {bt.fmt}"
        let tn := fundNat t n
        let tn' := fundNat t (n + 1)
        for b in bachCands t tn tn' do
          if isNFF b && lt' tn b && le' b tn' && !le' tn (fund b zero) then
            st := st.modify 4 (· + 1)
            if st[4]! < 4 then
              out.putStrLn s!"T-FAIL: t = {t.fmt}\n  b = {b.fmt}"
  | _ => pure ()
  return st

set_option maxHeartbeats 8000000 in
def probeA2f : IO Unit := do
  let out ← IO.getStdout
  let mut st : Array Nat := #[0, 0, 0, 0, 0]
  -- 塔・Ξ の種の格子
  let es : List Tm := [P M1p w, P M1p (add w one), P M1p M1, add (P M1p zero) (P M1p w), P M1p (O one),
    add M1 (P M1p w), M1, add M1 one, zero, one]
  for e in es do
    let σ := X1 e
    for X in [σ, add σ σ, add M1 σ, P M1p σ, add (P M1p zero) σ] do
      let S := P σ X
      let B := P σ (sc e)
      let mut pis : List Tm := []
      for base0 in [S, add S one, B] do
        for arg in [zero, one] do
          let f := P (O (sc base0)) arg
          pis := pis ++ [O (sc f), O (sc (add f one)), O (sc (O (sc f)))]
        pis := pis ++ [O (sc base0), O (sc (X1 base0)), O (sc (X1 (add (P M1p zero) base0))),
          O (sc (X1 (oadd (P M1p zero) (oadd M1 base0))))]
      let e0' := match (summands e) with
        | h :: _ => h
        | [] => zero
      pis := pis ++ [O (sc (X1 (oadd e0' S)))]
      for π in pis do
        let t := P π X
        if isNFF t then
          st ← checkA2 out t st
  out.putStrLn s!"probeA2f(grid): A2 {st[0]!}, nocof {st[1]!}, badseq {st[2]!}, idx fails {st[3]!}, t fails {st[4]!}"
  -- 一般の格子（probeA2 と同じ）
  let mut st2 : Array Nat := #[0, 0, 0, 0, 0]
  let extraPi : List Tm := [O (sc (P (X1 M1) (sc M1))), O (sc (add (P (X1 M1) (sc M1)) one)),
    O (sc (P (O (sc (sc (P (X1 M1) (sc M1))))) zero)), O (sc (add (P (O (sc (sc (P (X1 M1) (sc M1))))) zero) one)),
    O (sc (P (X1 M1p) (sc M1p))), O (sc (P (O (sc (sc (P (X1 M1p) (sc M1p))))) zero)),
    O (sc (P (X1 zero) one)), O (sc (P (O (sc (sc (P (X1 zero) one)))) zero))]
  let pis := dedupL (probePis ++ extraPi)
  let sigmas : List Tm := [X1 zero, X1 one, X1 M1, X1 (add M1 one), X1 M1p, X1 (P M1p zero), X1 w]
  let mut xs : List Tm := probeArgs
  for σ in sigmas do
    xs := xs ++ [σ, add σ σ, P M1p σ, add (P M1p zero) σ]
  xs := dedupL xs
  for π in pis do
    for X in xs do
      let t := P π X
      if isNFF t then
        st2 ← checkA2 out t st2
  out.putStrLn s!"probeA2f(general): A2 {st2[0]!}, nocof {st2[1]!}, badseq {st2[2]!}, idx fails {st2[3]!}, t fails {st2[4]!}"
  out.flush

def main (_args : List String) : IO Unit := probeA2f
