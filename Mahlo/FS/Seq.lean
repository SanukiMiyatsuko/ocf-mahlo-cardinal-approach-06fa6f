import Mahlo.FS.Def
import Mahlo.FS.Class

/-! 基本列の定義。

項 `t` の共終数 `dom t` と基本列 `fundNat t n`（共終数 `ω`）・`fundBig t ξ`（共終数が正則項 `σ`）。

* 和は最後の加数で決まる。正則項 `σ` は `σ[ξ] = base σ ⊕ ξ`。`Ω_c`（`c` 極限）は `Ω_{c[ξ]+1}`。
* 崩壊 `Ψ_π(X)`：
  - `X = 0`：`Ψ_{Ω_0}(0) = 1`、`Ψ_{Ω_{c+1}}(0) = Ω_c·ω`（`Ω_c·(n+2)`）。
  - 後者 `X = X' + 1`：`π = Ω_c` なら `Ψ_π(X')·(n+2)`。`π = Ξ_m(d)` なら目標の族の閉包（`famSeq`：`Ξ_m(ξ)`
    （`ξ < d`）と `Ω` についての閉包）で、種は `d < X'` なら `Ψ_π(X')`（`d < M_m` なら列は `Ψ_π(X')` の上の `Ω` の塔）、
    `X' = d`（底）なら目標の前線の最大の節点。
  - 極限 `X`：最後の加数の近似（`limitSeq`）。外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` なら、添字は `σ` の族の閉包
    （`outFix`、種は `a2Seed`）。
* `app τ g pre R r P c`：`g(pre ⊕ ((c ⊕ R[ν]) # P))`。`R` の共終数が `τ` 以上の正則項 `σ` なら対角化
  （添字 `gam`）。`iapp`：添字の列 `s` による対角化 `g(pre ⊕ ((c ⊕ R[s[ν]]) # P))`。

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
  /-- 正則項：共終数 `σ`、`[ξ] = b ⊕ ξ`。`σ = Ξ_m(q)` なら `qs` は `q` の加数とその列の記述 -/
  | reg (σ b : Tm) (qs : List (Tm × SeqD))
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
  /-- 添字の列 `s` による対角化：`[ν] = g(pre ⊕ ((c ⊕ R[s[ν]]) # P))`、`r` は `R` の列の記述。
      共終数は `s` の共終数（`ω` か正則項） -/
  | iapp (g : Gen) (pre : List Tm) (r : SeqD) (P c : Tm) (s : SeqD)
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

/-! ### 閉じた点 -/

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
  | .reg σ _ _ => .big σ
  | .add _ s => s.dom
  | .om s => s.dom
  | .app τ _ _ _ r _ _ =>
    match r.dom with
    | .big σ => if ltB σ τ then .big σ else .omega
    | _ => .omega
  | .iapp _ _ _ _ _ s =>
    match s.dom with
    | .big σ => .big σ
    | _ => .omega
  | _ => .omega

/-- 列の記述の、添字 `ξ`（正則項未満）の項 -/
def SeqD.big : SeqD → Tm → Tm
  | .shift s, ξ => s.big ξ
  | .reg _ b _, ξ => oadd b ξ
  | .add a s, ξ => oadd a (s.big ξ)
  | .om s, ξ => Om (sc (s.big ξ))
  | .app _ g pre _ r P c, ξ => g.ap (combine g pre c P (r.big ξ))
  | .iapp g pre r P c s, ξ => g.ap (combine g pre c P (r.big (s.big ξ)))
  | _, _ => zero

/-- 塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`（`X = pre + R`）の障害の探索。`top` なら節点 `z` は `M_m` 未満で、塔の
    閉包の分解（和・`Ω`・崩壊先・`Ξ_m(ζ)`（`ζ < X`）の引数の `M_m` についての前線）でたどり、分解できない
    節点（`Ξ_m(ζ)`（`ζ ≥ X`））と、分解の先に自身以上の障害を持つ節点のうち最大のものを返す（`z` の中に、
    それ以上の節点だけを通って見える）。`top` でなければ `Ξ_m(ζ)` の引数 `ζ` の中で `M_m` 未満の前線を探す -/
def kNd (m : Nat) (X : Tm) (top : Bool) (z : Tm) : Option Tm :=
  match top, z with
  | true, plus a b => maxOpt (kNd m X true a) (kNd m X true b)
  | true, Om e => kNd m X true e
  | true, Psi ρ a =>
    match kNd m X true ρ with
    | none => none
    | some u => some (if ltB u (Psi ρ a) then u else Psi ρ a)
  | true, Xi j ζ =>
    if j = m then
      if ltB ζ X then
        match kNd m X false ζ with
        | none => none
        | some u => some (if ltB u (Xi j ζ) then u else Xi j ζ)
      else some (Xi j ζ)
    else none
  | true, _ => none
  | false, plus a b => maxOpt (kNd m X false a) (kNd m X false b)
  | false, Om e => kNd m X false e
  | false, Xi j a => if ltB (Xi j a) (M m) then kNd m X true (Xi j a) else kNd m X false a
  | false, Psi p a =>
    if ltB (Psi p a) (M m) then kNd m X true (Psi p a)
    else maxOpt (kNd m X false p) (kNd m X false a)
  | false, _ => none
termination_by 2 * z.size + (if top then 0 else 1)
decreasing_by all_goals (simp only [Tm.size, ↓reduceIte]; omega)

/-- 目標 `τ` の前線の、塔（`X = pre + R`）の障害の最大のもの -/
def kNeed (m : Nat) (τ X : Tm) : Option Tm :=
  ((frB τ τ).map (kNd m X true)).foldr maxOpt none

/-- `M_m` の正準な塔の始点：目標の前線の障害の最大のもの `s`。`0` から始めた塔が 1 段目で `s` を越えるなら `0` -/
def kTop (τ : Tm) (m : Nat) (pre : List Tm) (R : Tm) (r : SeqD) : Tm :=
  match kNeed m τ (oadd (ofSummands pre) R) with
  | none => zero
  | some s => if ltB s (Xi m (oadd (ofSummands pre) (r.big zero))) then zero else s

/-- 対角化の近似の引数 -/
def argOf (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P γ : Tm) : Tm :=
  if canonK σ g pre R then combine g pre c P (r.big γ)
  else if outsideMode τ σ g pre R then combine g pre c P (r.big γ)
  else combine g pre c (if seedOut g && γ == zero then P else zero) (r.big γ)

/-- 目標 `τ` への崩壊の近似の有効性の調整（`mkApp` と同じ）：下限 `δ` が `pre` で始まる（`δ = pre ⊕ rt`）なら
    `rt + 1`、そうでなければ `0` -/
def adjOf (τ : Tm) (pre : List Tm) : Tm :=
  match tailRaw (argR? τ) pre with
  | none => zero
  | some rt => sc rt

/-- 対角化の添字。正準な塔（`canonK`・種を外に足す型）では種によらない塔、
    そうでなければ（目標そのものへの対角化・`Ξ` の族の閉包）種を始点に入れ、近似の値そのもので進める。
    外に足す型（`σ` が `M` でない）の塔は、`σ` への崩壊の近似にも有効性の調整 `c_σ = adjOf σ pre` を前に置く
    （`γ_{k+1} = Ψ_σ(pre ⊕ (c_σ ⊕ R[γ_k]))`、全て有効）。始点は `pre ⊕ R[0]` が `σ` の下限を越えれば `0`、
    越えなければ 1 段進めた `Ψ_σ(pre ⊕ (c_σ ⊕ R[0]))`（添字は `0` か `σ` の底より大きい主要項） -/
def gam (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P : Tm) : Nat → Tm
  | 0 =>
    if canonK σ g pre R then (match σ with | M m => kTop τ m pre R r | _ => zero)
    else if outsideMode τ σ g pre R then
      (match σ with
       | M _ => zero
       | _ =>
         if validR σ (oadd (ofSummands pre) (r.big zero)) then zero
         else col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big zero))) 0)
    else (match σ with | M _ => P | _ => if seedOut g then zero else P)
  | k + 1 =>
    let γ := gam τ σ g pre R r c P k
    if canonK σ g pre R then col σ (oadd (ofSummands pre) (r.big γ)) k
    else if outsideMode τ σ g pre R then
      match σ with
      | M _ => col σ (argOf τ σ g pre R r c P γ) k
      | _ => col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big γ))) k
    else g.ap (argOf τ σ g pre R r c P γ)

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
  | .iapp g pre r P c s, n => g.ap (combine g pre c P (r.big (s.nat n)))
  | _, _ => zero

/-- 列の 0 番目 -/
def SeqD.first (s : SeqD) : Tm :=
  match s.dom with
  | .big _ => s.big zero
  | _ => s.nat 0

/-! ### 崩壊の列の記述 -/

/-- `app` を作る（引数の下限で塞がるなら `none`）。目標が `Ξ_m(δ)` で下限 `δ` が `pre` で始まる（`δ = pre ⊕ rt`）なら、
    調整 `rt + 1` を前に置く（近似は `δ + 1 + R[ν]`、全て下限を越える） -/
def mkApp (ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) : Option SeqD :=
  if P ≠ zero ∧ ltB P R = false then none
  else
    match g.tgt? with
    | some τ =>
      match tailRaw (argR? τ) pre with
      | none => some (.app ceil g pre R r P zero)
      | some rt => if leB R rt then none else some (.app ceil g pre R r P (sc rt))
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

/-- 目標の族（`Ξ_m(q)` のときだけ）の、種 `P` より上の閉包（値は `ceil` 未満） -/
def famSeq (πf : Fam) (ceil : Tm) (P : Option Tm) : SeqD :=
  match πf with
  | .xi m q qs => mahloVK m q qs ceil P
  | _ => .none

/-- 列の記述の共終数（正則項）の族：`R` の列の記述は、共終数 `σ` の記述 `reg σ _ qs` を中に持つ -/
def SeqD.famOf : SeqD → Fam
  | .reg σ _ qs =>
    match σ with
    | Xi m q => .xi m q qs
    | Om _ => .om
    | _ => .none
  | .add _ s => s.famOf
  | .om s => s.famOf
  | .app _ _ _ _ r _ _ => r.famOf
  | .shift s => s.famOf
  | .iapp _ _ _ _ _ s => s.famOf
  | _ => .none

/-- `σ` への崩壊 `Ψ_σ(·)` か -/
def collOf (σ : Tm) : Tm → Bool
  | Psi ρ _ => ρ == σ
  | _ => false

/-- 外に足す型の対角化の族の閉包の種：目標 `τ` の前線の中で見える `Ψ_σ(·)` の最大のもの（それが `σ` の始点
    `Ψ_σ(e+1)` 未満・存在しないなら始点）。種は `σ` の族について閉じた点 `Ψ_σ(β)` なので、閉包の列は項
    `Ψ_σ(β+1)` の基本列そのもので（区間は Bachmann 性を壊さない）、`τ` の前線は全てその列の下にある -/
def a2Seed (σ τ : Tm) : Tm := maxO (some (frCl (collOf σ) τ)) (base σ)

/-- 外に足す型の対角化（`σ = Ξ_m(e)` への崩壊の塔）で `Ψ_σ(X) < Ψ_τ(X)` のとき：引数が `X` 未満の
    `Ψ_σ(·)` は全て `Ψ_τ(X)` 未満で塔は `Ψ_τ(X)` を越えないので、添字は目標 `τ` の前線の中の `σ` の族について
    閉じた点（`a2Seed`）の上の `σ` の族の閉包（`famSeq`）にする -/
def outFix : SeqD → SeqD
  | .app τ g pre R r P c =>
    match r.dom with
    | .big σ =>
      match σ with
      | Xi _ _ =>
        if !ltB σ τ && outsideMode τ σ g pre R &&
            ltB (Psi σ (oadd (ofSummands pre) R)) (Psi τ (oadd (ofSummands pre) R)) then
          .iapp g pre r P c (famSeq r.famOf σ (some (a2Seed σ τ)))
        else .app τ g pre R r P c
      | _ => .app τ g pre R r P c
    | _ => .app τ g pre R r P c
  | s => s

/-- 極限 `X`（加数 `xs`）の崩壊の列：最後の加数の近似。`X` の真の部分項で `Ψ_τ(X)` 未満のものは
    0 番目の近似で既に越えている（隙間）ので、種の挿入は要らない -/
def limitSeq (τ : Tm) (ceil : Tm) (xs : DL) : SeqD :=
  ((mkApp ceil (.psi τ) (preT xs) (lastT xs) (lastS xs) zero zero).map outFix).getD .none

/-- 崩壊 `Ψ_π(X)` の列（`πf` は `π` の族、`xs` は `X` の加数） -/
def cseq (π : Tm) (πf : Fam) (X : Tm) (xs : DL) : SeqD :=
  if X = zero then
    match π with
    | Om c => if c = zero then .one else .mul (omOf (pred c)) 2
    | _ => .none
  else
    match (lastS xs).dom with
    | .one =>
      if validR π (pred X) then
        match π with
        | Xi _ _ => famSeq πf π (some (Psi π (pred X)))
        | _ => .mul (Psi π (pred X)) 2
      else famSeq πf π (maxL (frB π π))
    | _ => limitSeq π π xs

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
    let s : SeqD := .reg (M n) (base (M n)) []
    ⟨s, [(M n, s)], .none⟩
  | plus a b =>
    let ia := info a
    let ib := info b
    ⟨.add a ib.seq, (a, ia.seq) :: ib.sums, .none⟩
  | Om c =>
    let s : SeqD :=
      if c = zero ∨ isSucc c = true then .reg (Om c) (base (Om c)) [] else .om (info c).seq
    ⟨s, [(Om c, s)], .om⟩
  | Xi m q =>
    let iq := info q
    let s : SeqD := .reg (Xi m q) (base (Xi m q)) iq.sums
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
