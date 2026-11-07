import Mahlo.FS.Def
import Mahlo.FS.Class

/-! 基本列の定義。

項 `t` の共終数 `dom t` と基本列 `fundNat t n`（共終数 `ω`）・`fundBig t ξ`（共終数が正則項 `σ`）。

* 和は最後の加数で決まる。正則項 `σ` は `σ[ξ] = base σ ⊕ ξ`。`Ω_c`（`c` 極限）は `Ω_{c[ξ]+1}`。
* 崩壊 `Ψ_π(X)`：
  - `X = 0`：`Ψ_{Ω_0}(0) = 1`、`Ψ_{Ω_{c+1}}(0) = Ω_c·ω`（`Ω_c·(n+1)`）。
  - 後者 `X = X' + 1`：`π = Ω_c` なら `Ψ_π(X')·(n+1)`。`π = Ξ_m(d)` なら、`d < X'` で `Ψ_π(X')` の上の
    `Ω` の塔、`X' = d`（底）なら目標の族の閉包（`famSeq`：`Ξ_m(ξ)`（`ξ < d`）の閉包）。
  - 極限 `X`：最後の加数の近似。前線の最大の節点を種とし、近似が種を越えなければ種を挿入する（`limitSeq`）。
* `app τ g pre R r P c`：`g(pre ⊕ ((c ⊕ R[ν]) # P))`。`R` の共終数が `τ` 以上の正則項 `σ` なら対角化
  （添字 `gam`）。

計算の仕組み：列の記述は部分項の列の記述を中に持つ（`app` の `r` は `R` の記述）。`info` が項を下から一度だけ
たどって全ての節点の記述を作るので、部分項の列を作り直すことはない。`t[n]` の計算は記述の木を下るだけ。 -/

namespace MahloOCF.FS

open Tm

/-- 近似の生成関数 -/
inductive Gen where
  | psi (π : Tm)
  | xi (m : Nat)

def Gen.ap : Gen → Tm → Tm
  | .psi π, δ => Psi π δ
  | .xi m, δ => Xi m δ

/-- 引数に下限のある崩壊の目標 -/
def Gen.tgt? : Gen → Option Tm
  | .psi π => some π
  | _ => none

/-- 列の記述。部分項 `R` の列は記述 `r` として中に持つ -/
inductive SeqD where
  /-- 列なし（`0`） -/
  | none
  /-- 後者 -/
  | one
  /-- 正則項：共終数 `σ`、`[ξ] = b ⊕ ξ` -/
  | reg (σ b : Tm)
  /-- `a + s` -/
  | add (a : Tm) (s : SeqD)
  /-- `Ω_c`（`c` 極限）：`[ξ] = Ω_{c[ξ]+1}` -/
  | om (s : SeqD)
  /-- `[n] = B·(n+k)` -/
  | mul (B : Tm) (k : Nat)
  /-- `[n] = Ω` の塔の `n+1` 段目 -/
  | tower (G : Tm)
  /-- `g(pre ⊕ ((c ⊕ R[ν]) # P))`、`r` は `R` の列の記述、`τ` は値の上限（共終数の判定） -/
  | app (τ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm)
  /-- 列を一つずらす（`[n] = s[n+1]`） -/
  | shift (s : SeqD)
  deriving Inhabited

/-- 加数とその列の記述の並び -/
abbrev DL := List (Tm × SeqD)

/-- 目標の族の記述：`Ξ_m(q)` は `q` の加数 -/
inductive Fam where
  | om
  | xi (m : Nat) (q : Tm) (qs : DL)
  | none

def lastT (l : DL) : Tm := (l.getLast?.map Prod.fst).getD zero
def lastS (l : DL) : SeqD := (l.getLast?.map Prod.snd).getD .none
def preT (l : DL) : List Tm := l.dropLast.map Prod.fst

/-- `th` より大きい最後の加数で分ける -/
def splitGtD (th : Tm) (ys : DL) : Option (List Tm × Tm × SeqD) :=
  match (ys.takeWhile (fun s => ltB th s.1)).getLast? with
  | none => none
  | some (R, r) => some ((ys.takeWhile (fun s => ltB th s.1)).dropLast.map Prod.fst, R, r)

/-- `τ` 以上の最後の加数で分ける -/
def splitPosD (τ : Tm) (ys : DL) : Option (List Tm × Tm × SeqD) :=
  match (ys.takeWhile (fun s => leB τ s.1)).getLast? with
  | none => none
  | some (R, r) => some ((ys.takeWhile (fun s => leB τ s.1)).dropLast.map Prod.fst, R, r)

/-- 近似 `pre ⊕ (c, P, x)`。ψ への崩壊では有効性の調整 `c` を前に置く（`c + x`、吸収あり）。
    Ξ では自然な和 -/
def combine (g : Gen) (pre : List Tm) (c P x : Tm) : Tm :=
  match g with
  | .psi _ => oadd (ofSummands pre) (nsum (oadd c x) P)
  | .xi _ => oadd (ofSummands pre) (nsum c (nsum P x))

/-! ### 対角化の塔の始点（閉じた点） -/

/-- `M_m` の族について閉じた点（それ未満の `ξ` の `Ξ_m(ξ)` は全てそれ未満）：`Ξ_m(w)`（`w ≥ M_m`）と、
    その族を目標に持つ崩壊 -/
def closedPt (m : Nat) : Tm → Bool
  | Xi m' w => m' == m && leB (M m) w
  | Psi ρ _ => closedPt m ρ
  | _ => false

/-- `x` が `e` の中に、`x` 以上の節点だけを通って現れる -/
def selfVis (x : Tm) : Tm → Bool
  | plus a b => selfVis x a || selfVis x b
  | Om a => selfVis x a
  | Xi m a => Xi m a == x || (leB x (Xi m a) && selfVis x a)
  | Psi p a => Psi p a == x || (leB x (Psi p a) && (selfVis x p || selfVis x a))
  | _ => false

/-- `t` の中の、値が `ub` 以下で `cl` を満たす節点のうち、`ub` の中で見えるものの最大のもの -/
def maxCl (cl : Tm → Bool) (ub : Tm) : Tm → Option Tm
  | plus a b => maxOpt (maxCl cl ub a) (maxCl cl ub b)
  | Om a => maxCl cl ub a
  | Xi m' a =>
    maxOpt (if cl (Xi m' a) && leB (Xi m' a) ub && selfVis (Xi m' a) ub then some (Xi m' a) else none)
      (maxCl cl ub a)
  | Psi p a =>
    maxOpt (if cl (Psi p a) && leB (Psi p a) ub && selfVis (Psi p a) ub then some (Psi p a) else none)
      (maxOpt (maxCl cl ub p) (maxCl cl ub a))
  | _ => none

/-- `t` の中の `Ξ_m` で閉じた節点の最大のもの -/
def maxXiClosed (m : Nat) (ub : Tm) : Tm → Option Tm := maxCl (closedPt m) ub

/-- `M_m` の塔の始点：調整 `c`・種 `P` の中の `Ξ_m` で閉じた点の最大のもの -/
def kStart (m : Nat) (c P : Tm) : Tm := (maxOpt (maxXiClosed m c c) (maxXiClosed m P P)).getD zero

/-- `σ` への崩壊の塔（上端 `T`）で閉じた点：`Ψ_σ(w)`（`w ≥ T`） -/
def closedS (σ T : Tm) : Tm → Bool
  | Psi ρ w => ρ == σ && leB T w
  | _ => false

/-- 種を外に足す型の塔の始点：調整 `c`・種 `P` の中の閉じた点の最大のもの -/
def sStart (σ T c P : Tm) : Tm :=
  (maxOpt (maxCl (closedS σ T) c c) (maxCl (closedS σ T) P P)).getD zero

/-- 目標 `τ` の前線の中の、`cl` を満たす点の最大のもの -/
def frCl (cl : Tm → Bool) (τ : Tm) : Tm :=
  (((frB τ τ).map (fun e => maxCl cl e e)).foldr maxOpt none).getD zero

/-- `M_m` の対角化で、近似が `M_m⁺` を越えうる（仮想的な崩壊 `virtK` を使う） -/
def kOld (m : Nat) (pre : List Tm) (R : Tm) : Bool := leB (succM m) (oadd (ofSummands pre) R)

/-- 対角化で種を外に足すか（添字は正準な塔）。`σ` が目標そのもの・`Ξ` の族の閉包では種を中に入れる -/
def outsideMode (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) : Bool :=
  match σ, g with
  | M m, .psi _ => kOld m pre R
  | M _, _ => false
  | _, _ => if σ = g.tgt?.getD τ then false else true

/-- ψ への `M_m` の対角化（近似が `M_m⁺` 未満）：添字は正準な `Ξ` の塔 -/
def canonK (σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) : Bool :=
  match σ, g with
  | M m, .psi _ => !kOld m pre R
  | _, _ => false

/-- ψ への崩壊の生成。目標そのものへの対角化では、0 番目の近似に種を自然な和で足す -/
def seedOut : Gen → Bool
  | .psi _ => true
  | _ => false

/-- 対角化での `σ` への崩壊（`k` は段の番号） -/
def col (σ δ : Tm) (k : Nat) : Tm :=
  match σ with
  | M m => if leB δ (succM m) then Xi m δ else virtK m k
  | _ => if validR σ δ then Psi σ δ else base σ

/-! ### 列の記述の評価（記述の木を下るだけ） -/

/-- 列の記述の共終数 -/
def SeqD.dom : SeqD → Cof Tm
  | .none => .zero
  | .shift s => s.dom
  | .one => .one
  | .reg σ _ => .big σ
  | .add _ s => s.dom
  | .om s => s.dom
  | .app τ _ _ _ r _ _ =>
    match r.dom with
    | .big σ => if ltB σ τ then .big σ else .omega
    | _ => .omega
  | _ => .omega

/-- 列の記述の、添字 `ξ`（正則項未満）の項 -/
def SeqD.big : SeqD → Tm → Tm
  | .shift s, ξ => s.big ξ
  | .reg _ b, ξ => oadd b ξ
  | .add a s, ξ => oadd a (s.big ξ)
  | .om s, ξ => Om (sc (s.big ξ))
  | .app _ g pre _ r P c, ξ => g.ap (combine g pre c P (r.big ξ))
  | _, _ => zero

/-- 対角化の近似の引数 -/
def argOf (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P γ : Tm) : Tm :=
  if canonK σ g pre R then combine g pre c P (r.big γ)
  else if outsideMode τ σ g pre R then combine g pre c P (r.big γ)
  else combine g pre c (if seedOut g && γ == zero then P else zero) (r.big γ)

/-- 対角化の添字。正準な塔（`canonK`・種を外に足す型）では種によらない塔、
    そうでなければ種を始点に入れ、値の帰還（`col` と値の大きい方）で進める -/
def gam (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P : Tm) : Nat → Tm
  | 0 =>
    if canonK σ g pre R then (match σ with | M m => kStart m c P | _ => zero)
    else if outsideMode τ σ g pre R then
      (match σ with
       | M _ => zero
       | _ => if seedOut g then sStart σ (oadd (ofSummands pre) R) c P else zero)
    else (match σ with | M _ => P | _ => if seedOut g then zero else P)
  | k + 1 =>
    let γ := gam τ σ g pre R r c P k
    if canonK σ g pre R then col σ (oadd (ofSummands pre) (r.big γ)) k
    else if outsideMode τ σ g pre R then
      match σ with
      | M _ => col σ (argOf τ σ g pre R r c P γ) k
      | _ => col σ (oadd (ofSummands pre) (r.big γ)) k
    else
      let A := argOf τ σ g pre R r c P γ
      let cl := col σ A k
      if ltB cl (g.ap A) && ltB (g.ap A) σ then g.ap A else cl

/-- 列の記述の `n` 番目 -/
def SeqD.nat : SeqD → Nat → Tm
  | .shift s, n => s.nat (n + 1)
  | .add a s, n => oadd a (s.nat n)
  | .om s, n => Om (sc (s.nat n))
  | .mul B k, n => mulNat B (n + k)
  | .tower G, n => FS.tower G (n + 1)
  | .app τ g pre R r P c, n =>
    match r.dom with
    | .big σ => if ltB σ τ then zero else g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P n))
    | _ => g.ap (combine g pre c P (r.nat n))
  | _, _ => zero

/-- 列の 0 番目 -/
def SeqD.first (s : SeqD) : Tm :=
  match s.dom with
  | .big _ => s.big zero
  | _ => s.nat 0

/-! ### 崩壊の列の記述 -/

/-- 有効性の調整：`rt` の、最初の近似を有効にする最短の先頭部分（なければ `rt + 1`） -/
def adjC (τ : Tm) (approx : Tm → Tm) (rt : Tm) : Tm :=
  match ((List.range ((summands rt).length + 1)).map (fun k => ofSummands ((summands rt).take k))).find?
      (fun c => validR τ (approx c)) with
  | some c => c
  | none => sc rt

/-- 対角化の調整：目標の前線の中の、塔で閉じた点の最大のもの -/
def kAdj (τ ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) : Tm :=
  match r.dom with
  | .big (M m) =>
    if !ltB (M m) ceil && canonK (M m) g pre R then frCl (closedPt m) τ else zero
  | .big σ =>
    if !ltB σ ceil && outsideMode ceil σ g pre R then
      frCl (closedS σ (oadd (ofSummands pre) R)) τ
    else zero
  | _ => zero

/-- `app` を作る（引数の下限で塞がるなら `none`） -/
def mkApp (ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) : Option SeqD :=
  if P ≠ zero ∧ ltB P R = false then none
  else
    match g.tgt? with
    | some τ =>
      let k := kAdj τ ceil g pre R r
      match tailRaw (argR? τ) pre with
      | none => some (.app ceil g pre R r P k)
      | some rt =>
        if leB R rt then none
        else
          let x0 := r.first
          let approx := fun c => combine g pre c P x0
          if validR τ (approx k) then some (.app ceil g pre R r P k)
          else some (.app ceil g pre R r P (oadd (adjC τ (fun c => approx (oadd c k)) rt) k))
    | _ => some (.app ceil g pre R r P c)

/-- `Ξ_m(ξ)`（`ξ < q`）の閉包（`qs` は `q` の加数、種 `P`、値は `ceil` 未満） -/
def mahloVK (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) : SeqD :=
  if q = zero then .tower (maxO P (floorLev m))
  else if isSucc q then
    let s := maxO P (Xi m (pred q))
    match splitPosD ceil qs.dropLast with
    | some (pre, R, r) =>
      match mkApp ceil (.xi m) pre R r s zero with
      | some sq => sq
      | none => .tower s
    | none => .tower s
  else
    let s0 : SeqD := .app ceil (.xi m) (preT qs) (lastT qs) (lastS qs) zero zero
    match P with
    | none => s0
    | some p =>
      if ltB p s0.first then s0
      else if s0.first = p then .app ceil (.xi m) (preT qs) (lastT qs) (.shift (lastS qs)) zero zero
      else
        match splitGtD p qs with
        | some (pre, R, r) =>
          match mkApp ceil (.xi m) pre R r p zero with
          | some sq => sq
          | none => .tower p
        | none => .tower p

/-- 目標の族の、種 `P` より上の閉包（値は `ceil` 未満） -/
def famSeq (πf : Fam) (ceil : Tm) (P : Option Tm) : SeqD :=
  match πf with
  | .om =>
    match P with
    | some p => .mul p 2
    | none => .none
  | .xi m q qs => mahloVK m q qs ceil P
  | .none => .none

/-- 極限の引数（加数 `ys`）への種 `p` の挿入 -/
def insertAtL (τ : Tm) (τf : Fam) (ceil p : Tm) (ys : DL) : SeqD :=
  match splitGtD p ys with
  | some (pre, R, r) =>
    match mkApp ceil (.psi τ) pre R r p zero with
    | some s => s
    | none => famSeq τf ceil (some p)
  | none => famSeq τf ceil (some p)

/-- 極限 `X`（加数 `xs`）の崩壊の列 -/
def limitSeq (τ : Tm) (τf : Fam) (ceil X : Tm) (xs : DL) : SeqD :=
  let plain := (mkApp ceil (.psi τ) (preT xs) (lastT xs) (lastS xs) zero zero).getD .none
  match maxL (frB τ X) with
  | none => plain
  | some p =>
    if ltB p plain.first then plain
    else if plain.first = p then
      (mkApp ceil (.psi τ) (preT xs) (lastT xs) (.shift (lastS xs)) zero zero).getD .none
    else insertAtL τ τf ceil p xs

/-- 崩壊 `Ψ_π(X)` の列（`πf` は `π` の族、`xs` は `X` の加数） -/
def cseq (π : Tm) (πf : Fam) (X : Tm) (xs : DL) : SeqD :=
  if X = zero then
    match π with
    | Om c => if c = zero then .one else .mul (omOf (pred c)) 1
    | _ => .none
  else
    match (lastS xs).dom with
    | .one =>
      if validR π (pred X) then
        match π with
        | Xi _ _ => .tower (Psi π (pred X))
        | _ => .mul (Psi π (pred X)) 1
      else famSeq πf π (maxL (frB π π))
    | _ => limitSeq π πf π X xs

/-! ### 項の解析 -/

/-- 項の解析：自身の列の記述・加数ごとの記述・目標の族の記述 -/
structure Info where
  seq : SeqD
  sums : DL
  fam : Fam

/-- 項を下から一度だけたどり、全ての節点の列の記述を作る -/
def info : Tm → Info
  | zero => ⟨.none, [], .none⟩
  | M n =>
    let s : SeqD := .reg (M n) (base (M n))
    ⟨s, [(M n, s)], .none⟩
  | plus a b =>
    let ia := info a
    let ib := info b
    ⟨.add a ib.seq, (a, ia.seq) :: ib.sums, .none⟩
  | Om c =>
    let s : SeqD :=
      if c = zero ∨ isSucc c = true then .reg (Om c) (base (Om c)) else .om (info c).seq
    ⟨s, [(Om c, s)], .om⟩
  | Xi m q =>
    let iq := info q
    let s : SeqD := .reg (Xi m q) (base (Xi m q))
    ⟨s, [(Xi m q, s)], .xi m q iq.sums⟩
  | Psi π X =>
    let iπ := info π
    let iX := info X
    let s : SeqD := cseq π iπ.fam X iX.sums
    ⟨s, [(Psi π X, s)], .none⟩

/-- 共終数 -/
def dom (t : Tm) : Cof Tm := (info t).seq.dom

/-- 共終数が正則項の場合の基本列 -/
def fundBig (t ξ : Tm) : Tm := (info t).seq.big ξ

/-- 共終数が `ω` の場合の基本列 -/
def fundNat (t : Tm) (n : Nat) : Tm := (info t).seq.nat n

/-- 基本列 -/
def fund (t ξ : Tm) : Tm :=
  let s := (info t).seq
  match s.dom with
  | .zero => zero
  | .one => pred t
  | .omega => s.nat (natOf ξ)
  | .big σ => s.big (if ltB ξ σ then ξ else zero)

end MahloOCF.FS
