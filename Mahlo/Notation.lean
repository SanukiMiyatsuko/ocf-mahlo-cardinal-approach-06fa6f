/-!
# Mahlo 基数の列にもとづく加法的な記法系

Rathjen, *Ordinal notations based on a weakly Mahlo cardinal*（1990）の記法系から Veblen 関数を抜き、
閉包を加法だけにした系。Compact リポジトリの弱コンパクト版（`RTKA`）と同じ同時再帰の形をとり、
`Ψ` は Buchholz 型（崩壊先ごとの底の条件 `Base_π`）にしてある。意味論は `Mahlo/Setting.lean`。

項は 6 種類：
* `zero`、`M n`（`n ≥ 1`、弱 Mahlo 基数の増加列 `M_1 < M_2 < ⋯` の第 `n` 項）
* `plus a b`（`a + b`、`a` は和でない 0 以外の項、`b ≠ 0`）
* `Om a`（`Ω_a = ℵ_{1+a}`）
* `Xi n a`（`Ξ_n(a)`：`M_n` への Mahlo 崩壊）
* `Psi pi a`（`Ψ_π(a)`：正則な項 `π` への崩壊）

`1` は定数でなく `one := Ψ_{Ω_0}(0)` で表す。

比較は、和は辞書式、和でない項は階（`M_{n-1} ≤ x < M_n` となる `n`）で比べ、同じ階では

* `Ξ` どうしは Lemma 4.14、
* `Ψ` と `Ξ`、異なる崩壊先の `Ψ` どうしは分離補題（`Mahlo/Compare.lean` の `sep`）から
  「崩壊先 `σ` の底の条件 `Base_σ` を満たすか」で、
* 同じ崩壊先の `Ψ` どうしは引数で

比べる。`cmp`・`inC`・`isNF` は停止性を証明した全域関数（測度は
`(引数の大きさの最大, 大きさの和, 段)` の辞書式順序）。 -/

namespace MahloOCF

inductive Tm where
  | zero
  /-- `M_n`（`n ≥ 1`） -/
  | M (n : Nat)
  /-- `a + b` -/
  | plus (a b : Tm)
  /-- `Ω_a` -/
  | Om (a : Tm)
  /-- `Ξ_n(a)` -/
  | Xi (n : Nat) (a : Tm)
  /-- `Ψ_π(a)` -/
  | Psi (pi a : Tm)
  deriving DecidableEq, Inhabited

open Tm

/-- `1 = Ψ_{Ω_0}(0)` -/
def one : Tm := Psi (Om zero) zero

def summands : Tm → List Tm
  | zero => []
  | plus a b => a :: summands b
  | t => [t]

def ofSummands : List Tm → Tm
  | [] => zero
  | [a] => a
  | a :: rest => plus a (ofSummands rest)

def isPrincipal : Tm → Bool
  | zero | plus _ _ => false
  | _ => true

theorem summands_plus (a b : Tm) : summands (.plus a b) = a :: summands b := rfl

theorem summands_principal {t : Tm} (h : isPrincipal t = true) : summands t = [t] := by
  cases t <;> simp_all [isPrincipal, summands]

/-- 最後の加数が `1` -/
def isSucc (c : Tm) : Bool := (summands c).getLast? == some one

/-- 最後の加数 `1` を除いたもの（`isSucc c` のとき `c = predT c + 1`） -/
def predT (c : Tm) : Tm := ofSummands (summands c).dropLast

/-- `M_n` を表す項（`M_0 = 0`） -/
def kTerm (m : Nat) : Tm := if m = 0 then zero else M m

/-- 階：`M_{n-1} ≤ x < M_n` となる `n`（`M_0 = 0`）。`0` は `0` -/
def lev : Tm → Nat
  | zero => 0
  | M n => n + 1
  | plus a _ => lev a
  | Om a => max 1 (lev a)
  | Xi n _ => n
  | Psi pi _ => lev pi

/-- `Ψ` の崩壊先になる正則な項（`Ω_0`、`Ω_{ζ+1}`、`Ξ_n(a)`） -/
def isRegTerm : Tm → Bool
  | Om c => c == zero || isSucc c
  | Xi _ _ => true
  | _ => false

def isXi : Tm → Bool
  | Xi _ _ => true
  | _ => false

/-- `Ω_X = X` となる項（`M_n`、`Ξ`、`Ξ` への `Ψ`） -/
def omegaFixed : Tm → Bool
  | M _ | Xi _ _ => true
  | Psi pi _ => isXi pi
  | _ => false

/-- `Ω_ζ` を表す項（`ζ` が `Ω` の不動点なら `ζ` 自身） -/
def omOf (ζ : Tm) : Tm := if omegaFixed ζ then ζ else Om ζ

/-- 項の大きさ -/
def Tm.size : Tm → Nat
  | zero | M _ => 1
  | plus a b => a.size + b.size + 1
  | Om a => a.size + 1
  | Xi _ a => a.size + 1
  | Psi pi a => pi.size + a.size + 1

def lsize : List Tm → Nat
  | [] => 0
  | t :: ts => t.size + lsize ts

theorem Tm.size_pos (t : Tm) : 0 < t.size := by
  cases t <;> simp only [Tm.size] <;> omega

theorem lsize_summands_le (t : Tm) : lsize (summands t) ≤ t.size := by
  induction t with
  | zero => simp [summands, lsize]
  | plus a b _ ihb => simp only [summands, lsize, Tm.size]; omega
  | _ => simp [summands, lsize]

theorem lsize_append (l l' : List Tm) : lsize (l ++ l') = lsize l + lsize l' := by
  induction l with
  | nil => simp [lsize]
  | cons a l ih => simp only [List.cons_append, lsize, ih]; omega

theorem lsize_summands_add_length (t : Tm) :
    lsize (summands t) + (summands t).length ≤ t.size + 1 := by
  induction t with
  | zero => simp [summands, lsize, Tm.size]
  | plus a b _ ihb =>
    simp only [summands, lsize, List.length_cons, Tm.size] at ihb ⊢
    omega
  | _ => simp only [summands, lsize, List.length_cons, List.length_nil, Tm.size]; omega

theorem size_ofSummands_le : ∀ l : List Tm, (ofSummands l).size ≤ lsize l + l.length + 1
  | [] => by simp [ofSummands, Tm.size, lsize]
  | [a] => by simp only [ofSummands, lsize, List.length_cons, List.length_nil]; omega
  | a :: b :: rest => by
    have ih := size_ofSummands_le (b :: rest)
    simp only [ofSummands, Tm.size, lsize, List.length_cons] at ih ⊢
    omega

theorem size_omOf_le (ζ : Tm) : (omOf ζ).size ≤ ζ.size + 1 := by
  unfold omOf
  split
  · omega
  · simp only [Tm.size]; omega

theorem kTerm_size (m : Nat) : (kTerm m).size = 1 := by
  unfold kTerm
  split <;> rfl

theorem summands_of_isSucc {c : Tm} (h : isSucc c = true) :
    ∃ ys, summands c = ys ++ [one] := by
  have hl : (summands c).getLast? = some one := by simpa [isSucc] using h
  exact List.getLast?_eq_some_iff.mp hl

theorem predT_of_summands {c : Tm} {ys : List Tm} (h : summands c = ys ++ [one]) :
    predT c = ofSummands ys := by
  simp [predT, h]

theorem size_predT_of_isSucc {c : Tm} (h : isSucc c = true) : (predT c).size + 3 ≤ c.size := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc h
  have h1 := lsize_summands_add_length c
  rw [hys, lsize_append] at h1
  have h2 := size_ofSummands_le ys
  rw [predT_of_summands hys]
  simp only [lsize, List.length_append, List.length_cons, List.length_nil, one, Tm.size] at h1
  omega

/-- `Ω_{c-1}` を表す項は `Ω_c` より小さい -/
theorem size_omOf_predT_lt {c : Tm} (h : isSucc c = true) :
    (omOf (predT c)).size < (Om c).size := by
  have := size_omOf_le (predT c)
  have := size_predT_of_isSucc h
  simp only [Tm.size]
  omega

/-- 辞書式順序の減少（`Classical.choice` を使わない形） -/
theorem lex3 {a b c a' b' c' : Nat} (h1 : a ≤ a') (h2 : a = a' → b ≤ b')
    (h3 : a = a' → b = b' → c < c') :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a, b, c) (a', b', c') := by
  cases Nat.lt_or_ge a a' with
  | inl h => exact Prod.Lex.left _ _ h
  | inr h =>
    have e : a = a' := Nat.le_antisymm h1 h
    subst e
    apply Prod.Lex.right
    cases Nat.lt_or_ge b b' with
    | inl hb => exact Prod.Lex.left _ _ hb
    | inr hb =>
      have e : b = b' := Nat.le_antisymm (h2 rfl) hb
      subst e
      exact Prod.Lex.right _ (h3 rfl rfl)

/-! 比較と `C(γ, δ)` への所属。 -/

mutual

def cmp (a b : Tm) : Ordering :=
  cmpList (summands a) (summands b)
termination_by (max a.size b.size, a.size + b.size, 6)
decreasing_by
  all_goals
    have := lsize_summands_le a
    have := lsize_summands_le b
    apply lex3 <;> intros <;> omega

def cmpList : List Tm → List Tm → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match cmpP x y with
    | .eq => cmpList xs ys
    | o => o
termination_by xs ys => (max (lsize xs) (lsize ys), lsize xs + lsize ys, 5)
decreasing_by
  all_goals
    simp only [lsize]
    have := Tm.size_pos x
    have := Tm.size_pos y
    apply lex3 <;> intros <;> omega

/-- 和でない 0 以外の項どうしの比較 -/
def cmpP (x y : Tm) : Ordering :=
  if lev x < lev y then .lt
  else if lev y < lev x then .gt
  else
    match x, y with
    -- 同じ階の `M` は `M_{n-1}` だけで、その階の他の項より小さい（`Ω_{M_{n-1}} = M_{n-1}` は除く）
    | M _, M _ => .eq
    | M m, Om b => if b == M m then .eq else .lt
    | Om b, M m => if b == M m then .eq else .gt
    | M _, _ => .lt
    | _, M _ => .gt
    | Om a, Om b => cmp a b
    | Om a, y => cmpOmX a y
    | x, Om b => (cmpOmX b x).swap
    | Xi n a, Xi m b =>
      if a == b then .eq else if xiLtXi (Xi n a) (Xi m b) then .lt else .gt
    | Psi pi a, Xi m b => if psiLtXi (Psi pi a) (Xi m b) then .lt else .gt
    | Xi m b, Psi pi a => if psiLtXi (Psi pi a) (Xi m b) then .gt else .lt
    | Psi pi a, Psi sg b => cmpPsi (Psi pi a) (Psi sg b)
    | _, _ => .eq
termination_by (max x.size y.size, x.size + y.size, 4)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

/-- `Ω_a` と同じ階の `X`（`Ξ` または `Ψ`）の比較 -/
def cmpOmX (a X : Tm) : Ordering :=
  if omegaFixed X then cmp a X
  else
    match X with
    -- `Ψ_{Ω_c}(β)`：`c = ζ + 1` なら `Ω_ζ < X < Ω_c`、`c = 0` なら `X < Ω_0`
    | Psi (Om c) _ => if cmp a c == .lt then .lt else .gt
    | _ => .gt
termination_by (max (a.size + 1) X.size, a.size + 1 + X.size, 3)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

/-- Lemma 4.14：同じ階の `Ξ_n(α) < Ξ_n(β)` -/
def xiLtXi (x y : Tm) : Bool :=
  match x, y with
  | Xi n a, Xi m b =>
    (cmp a b == .lt && inC a b (Xi m b)) || (cmp b a == .lt && !inC b a (Xi n a))
  | _, _ => false
termination_by (max x.size y.size, x.size + y.size, 3)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

/-- 同じ階の `Ψ_π(α) < Ξ_m(β)`：`π ≤ Ξ_m(β)` または `Ψ_π(α)` が `Ξ_m(β)` の底の条件を満たさない -/
def psiLtXi (x y : Tm) : Bool :=
  match x, y with
  | Psi pi a, Xi m b => cmp pi (Xi m b) != .gt || !(baseOf (Xi m b) (Psi pi a))
  | _, _ => false
termination_by (max x.size y.size, x.size + y.size, 3)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

/-- 同じ階の `Ψ` どうしの比較 -/
def cmpPsi (x y : Tm) : Ordering :=
  match x, y with
  | Psi pi a, Psi sg b =>
    if pi == sg then cmp a b
    else if cmp sg pi == .lt then (if baseOf sg (Psi pi a) then .gt else .lt)
    else (if baseOf pi (Psi sg b) then .lt else .gt)
  | _, _ => .eq
termination_by (max x.size y.size, x.size + y.size, 3)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

/-- 崩壊先 `σ` の底の条件 `Base_σ(t)` -/
def baseOf (σ t : Tm) : Bool :=
  match σ with
  | Om c =>
    if _h : isSucc c = true then cmp (omOf (predT c)) t == .lt
    else c == zero && t != zero
  | Xi m d => cmp (kTerm (m - 1)) t == .lt && inC d d t
  | _ => false
termination_by (max σ.size t.size, σ.size + t.size, 2)
decreasing_by
  · have := size_omOf_predT_lt _h
    simp only [Tm.size] at this
    simp only [Tm.size]
    apply lex3 <;> intros <;> omega
  · have := kTerm_size (m - 1)
    have := Tm.size_pos d
    simp only [Tm.size]
    apply lex3 <;> intros <;> omega
  · simp only [Tm.size]
    apply lex3 <;> intros <;> omega

/-- `α ∈ C(γ, δ)`（`a` の部分項のうち `δ` 以上のものが段 `γ` で作れるか） -/
def inC (a g d : Tm) : Bool :=
  match a with
  | zero | M _ => true
  | plus x y => inC x g d && inC y g d
  | Om x => inC x g d
  | Xi n b => cmp (Xi n b) d == .lt || (inC b g d && cmp b g == .lt)
  | Psi pi b =>
    cmp (Psi pi b) d == .lt || (inC pi g d && inC b g d && cmp b g == .lt)
termination_by (max a.size (max g.size d.size), a.size + max g.size d.size, 7)
decreasing_by all_goals (try simp only [Tm.size]); all_goals (apply lex3 <;> intros <;> omega)

end

def lt (a b : Tm) : Bool := cmp a b == .lt

/-- `M_n^+ = Ω_{M_n + 1}` -/
def succM (n : Nat) : Tm := Om (plus (M n) one)

/-- 標準形 -/
def isNF (t : Tm) : Bool :=
  match t with
  | zero => true
  | M n => n ≥ 1
  | plus a b =>
    isPrincipal a && b != zero && isNF a && isNF b &&
      (match summands b with
       | h :: _ => cmp h a != .gt
       | [] => false)
  | Om a => isNF a && !(omegaFixed a)
  | Xi n a => n ≥ 1 && isNF a && cmp a (succM n) != .gt && inC a a (M n)
  | Psi pi a =>
    isNF pi && isNF a && isRegTerm pi &&
      (match pi with
       | Xi _ d => lt d a
       | _ => true) &&
      inC a a (Psi pi a)

partial def Tm.fmt : Tm → String
  | zero => "0"
  | M n => s!"M{n}"
  | plus a b => s!"{a.fmt}+{b.fmt}"
  | Om a => s!"Ω_{fmtArg a}"
  | Xi n a => s!"Ξ{n}({a.fmt})"
  | Psi pi a => s!"Ψ_{fmtArg pi}({a.fmt})"
where
  fmtArg (t : Tm) : String :=
    match t with
    | plus .. => s!"({t.fmt})"
    | _ => t.fmt

instance : Repr Tm where
  reprPrec t _ := t.fmt

end MahloOCF
