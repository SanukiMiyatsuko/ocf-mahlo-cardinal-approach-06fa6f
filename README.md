# Mahlo

M. Rathjen, *Ordinal notations based on a weakly Mahlo cardinal*（Arch. Math. Logic 29, 1990）の記法系から
Veblen 関数を抜き、閉包を加法だけにした OCF と記法系。mathlib には依存しない。

## 設計

Compact リポジトリ（弱コンパクト版）と同じく、崩壊関数を一つの段 `α` についての同時再帰で定義する。

* 基数：弱 Mahlo 基数の増加列 `M_1 < M_2 < ⋯`（`Setting`）、`Λ = sup M_n`。
  `Ω_x = ℵ_{1+x}`（`Ω_0 = ℵ_1`）。
* `C(α, β)`：`β ∪ {M_m}` を `+`、`Ω`、`Ξ_m(ξ)`（`ξ < α`、`ξ ≤ M_m^+`）、`Ψ_π(δ)`（`δ < α`、`Ψ_π(δ) < π`、
  `δ ∈ C(δ, Ψ_π(δ))`）で閉じたもの。`M_m^+ = Ω_{M_m + 1}`（元論文の `χ` の添字 `< ε_{M+1}` にあたる上限）。
* `M^α = {ρ ∈ Reg : C(α, ρ) ∩ K(ρ) ⊆ ρ ∧ α ∈ C(α, ρ)}`、
  `Ξ_m(α) = min(M^α ∩ (M_{m-1}, M_m))`（`M_m` への Mahlo 崩壊）。
* `Ψ_π(α) = min{η < π : Base_π(η) ∧ C(α, η) ∩ π ⊆ η}`（Buchholz 型）。底の条件は崩壊先だけで決まる：
  `Base_{Ω_0}(η) ⟺ 0 < η`、`Base_{Ω_{ζ+1}}(η) ⟺ Ω_ζ < η`、
  `Base_{Ξ_m(δ)}(η) ⟺ M_{m-1} < η ∧ δ ∈ C(δ, η)`（`δ < α` のときだけ有効）。

記法系の項は `zero`・`M n`・`plus a b`・`Om a`・`Xi n a`・`Psi pi a` の 6 種類で、`1` は `Ψ_{Ω_0}(0)` で表す。
`Ξ_n(a)` の標準形は引数に上限 `a ≤ M_n^+` を課す。

## 証明したこと

### 意味論（弱 Mahlo 基数の列を仮定）

| 定理 | ファイル | 内容 |
|---|---|---|
| `Xi_lt` | `Basic.lean` | `α ∈ C(α, M_m)` なら `Ξ_m(α) < M_m`（Mahlo 性） |
| `Xi_lt_Xi_iff` | `Compare.lean` | Lemma 4.14（`Ξ` どうしの比較） |
| `sep` | `Compare.lean` | 分離補題：`κ < π` が崩壊先なら `Ψ_π(β) ≤ κ` のとき `¬ Base_κ(Ψ_π(β))` |
| `Psi_lt_target_iff` ほか | `Compare.lean` | `Ψ` と崩壊先・`Ψ` どうしの比較、`Ψ` の単射性 |
| `cmp_correct`・`inC_correct`・`baseOf_correct` | `Correct.lean` | `Good` な項について比較・`C` への所属・底の条件の判定が正しい |
| `isNF_iff_good` | `NF.lean` | 計算可能な `isNF` は意味論的な標準形 `Good` のちょうどの判定 |
| `cmp_correct_of_isNF`・`val_inj_of_isNF` | `NF.lean` | 標準形の上で `cmp` は値の比較と一致し、標準形は一意 |
| `Psi_succ_fs`・`fs_psi_succ` | `Succ.lean` | `π = Ω_0, Ω_{ζ+1}` なら `Ψ_π(β+1) = sup_n Ψ_π(β)·(n+1)`、記法系の基本列 |
| `nfValue_iff_C` | `Complete.lean` | 標準形の値の集合はちょうど `C(Λ, 0)` |
| `wellFounded_lt`・`lt_strictTotal` | `Complete.lean` | 弱 Mahlo 基数の列があれば、標準形の上の順序は整礎な狭義全順序 |

### 構文的な証明（仮定なし、公理は `propext`・`Quot.sound` だけ）

| 定理 | ファイル | 内容 |
|---|---|---|
| `swapY`・`eqY`・`transY`・`triY` | `WF/Order.lean` | 標準形の上で `cmp` は反対称で `.eq` なら等しく、`<` は推移的（狭義全順序） |
| `k2Y`・`k2tY`・`k2xY`・`cxY` | `WF/Order.lean` | 崩壊の引数・崩壊先の前線は崩壊の値より小さい、など |
| `wmax_of_good` | `WF/Wmax.lean` | `Good η`（`η ∈ C^η(Wmax)`、`C^η(Wmax) ∩ η ⊆ Wmax`）なら `η ∈ Wmax` |
| `acc_wk`・`coll_wk` | `WF/Wmax.lean` | `M_n^+` 以下の範囲 `WK n` は整礎で、その元を引数とする `Ξ_j`・`Ψ_π` は `Wmax` に入る |
| `wellFounded_isNF` | `WF/Wmax.lean` | **標準形全体の上の `<` は整礎** |
| `psi_pred_WNF`・`prin_le_psi_pred`・`fs_psi_succY` | `WF/Fund.lean` | `Ψ_π(b+1)`（`π = Ω_0, Ω_{ζ+1}`）が標準形なら `Ψ_π(b)` も標準形、`Ψ_π(b+1)` 未満の主要項は `Ψ_π(b)` 以下、基本列 `Ψ_π(b)·(n+1)` |
| `wellFounded_NFLt`・`lt_strictTotal_NF`・`cmp_eq_iff_NF`・`cmp_swap_NF`・`fs_psi_succ_NF` | `Unconditional.lean` | `Complete.lean`・`Succ.lean` の記法系についての主張（`wellFounded_lt`・`lt_strictTotal`・`cmp_eq_iff`・`fs_psi_succ`）を仮定なしで |

`cmp`・`isNF` は停止性を証明した全域関数で、`#print axioms` は `propext`・`Quot.sound` のみ。
構文的な証明（`Mahlo/WF`・`Unconditional.lean`）も同じで、`#guard_msgs` でビルド時に検査している。
`sorry` は無い。

### 仮定なしの順序数への値（`Unconditional.lean`）

整礎な狭義全順序から、標準形の値を始切片の順序型 `ordVal a`（`nfWellOrder` の `a` 未満の部分の型）で
定める。公理は `propext`・`Quot.sound` だけ。

| 定理 | 内容 | 対応する意味論の定理 |
|---|---|---|
| `cmp_ordVal` | `cmp` は値の比較と一致する | `cmp_correct_of_isNF` |
| `ordVal_inj` | 値が等しければ標準形も等しい | `val_inj_of_isNF` |
| `ordVal_range` | 値の集合はちょうど記法系の順序型 `nfOrderType` 未満の順序数 | `nfValue_iff_C`（値の集合 = `C(Λ, 0)`） |
| `ordVal_fs` | `Ψ_π(b+1)` の値は基本列 `Ψ_π(b)·(n+1)` の値の上限 | `Psi_succ_fs` |

### 二つの意味論の一致（`Agree.lean`）

| 定理 | 内容 |
|---|---|
| `setting_iff` | `Setting` は弱 Mahlo 基数の狭義増加列 `M_1 < M_2 < ⋯` そのもの（崩壊関数を定義するためのデータ） |
| `val_lt_iff_ordVal_lt`・`val_eq_iff_ordVal_eq` | どの `Setting` でも、崩壊関数による値 `val` と仮定なしの値 `ordVal` は標準形に同じ順序を与える |
| `closure_iso_orderType` | どの `Setting` でも、崩壊関数の閉包 `C(Λ, 0)` は順序を保って `nfOrderType` 未満の順序数と一対一に対応する |

## 設計の議論で求めた性質と、それを示した定理

設計の議論（`/goal` の前のやりとり）で述べた主張を順に挙げ、それを示した定理を対応させる。「仮定なし」の列は
大基数の仮定を使わず、公理も `propext`・`Quot.sound` だけ（`#guard_msgs` でビルドのたびに確認）の定理。
「`Setting` の下」の列は崩壊関数 `Ψ`・`Ξ` の値についての定理で、どの `Setting` についても成り立つ。

| 設計での主張 | 仮定なし | `Setting` の下 |
|---|---|---|
| 構成子は `zero`・`plus`・`M n`・`Om`・`Xi`・`Psi` の 6 個で、`1` は定義 `Ψ_{Ω_0}(0)` | `Tm`・`one`（`Notation.lean`） | — |
| `1 = Ψ_{Ω_0}(0)`（`C(0,1) ∩ ℵ_1 = {0}`） | `ordVal_lt_one`・`not_ordVal_lt_zero`（`Design.lean`） | `Psi_Om_zero_zero`（`Basic.lean`） |
| `Ξ_n(α) = min((M^α ∩ (M_{n-1}, M_n)) ∪ {M_n})` は `M_n` 未満で正則 | — | `Xi_lt`・`Xi_mem`・`XiGood`（`Basic.lean`） |
| Lemma 4.14（`Ξ` どうしの比較） | `ordVal_xi_xi`（`Design.lean`） | `Xi_lt_Xi_iff`・`Xi_inj`（`Compare.lean`） |
| (5.7) `C(β, Ψ_π(β)) ∩ π ⊆ Ψ_π(β)` | — | `Psi_spec`（`Setting.lean`） |
| (5.6) 分離補題 | — | `sep`（`Compare.lean`） |
| 同じ崩壊先：`Ψ_π(a) < Ψ_π(b) ⟺ a < b` | `ordVal_psi_same`（`Design.lean`） | `Psi_lt_Psi_same`（`Compare.lean`） |
| `σ < π`：`Ψ_π(a) < Ψ_σ(b) ⟺ ¬Base_σ(Ψ_π(a))` | `ordVal_psi_psi_of_target_lt`・`ordVal_psi_psi_of_lt_target`（`Design.lean`） | `Psi_lt_Psi_iff_lt`・`Psi_lt_Psi_iff_gt`（`Compare.lean`） |
| `κ < π` が正則：`Ψ_π(a) < κ ⟺ ¬Base_κ(Ψ_π(a))` | `ordVal_psi_xi_of_lt_target`（`Design.lean`） | `Psi_lt_target_iff`（`Compare.lean`） |
| 比較は `inC`・`baseOf` の判定に帰着し、計算できる | `cmp`・`inC`・`baseOf`・`isNF`（`Notation.lean`）と `cmp_ordVal` | `cmp_correct_of_isNF`（`NF.lean`） |
| 標準形の条件（`π = Ξ_n(d)` なら `d < a`、`a ∈ C(a, Ψ_π(a))`）、単射性 | `cmp_eq_iff_NF`・`ordVal_inj` | `isNF_iff_good`・`val_inj_of_isNF`（`NF.lean`） |
| 後続基数への崩壊 `Ψ_π(β+1)[n] = Ψ_π(β)·(n+1)` | `fs_psi_succ_NF`・`ordVal_fs`（`Unconditional.lean`） | `Psi_succ_fs`・`fs_psi_succ`（`Succ.lean`） |
| 到達不能基数への崩壊では `·ω` にできない（`Ω` の入れ子が挟まる） | `psi_xi_fs_not_cofinal`（`Design.lean`） | — |
| 有効性の制限は Rathjen 型の条件 `π ∈ C(α,ρ)` と同じ制限 | — | `Xi_mem_C_iff`・`rathjen_no_candidate`・`Psi_rathjen_condition`（`Design.lean`） |
| 完全性：`C(Λ,0)` の元は全て標準形の値 | `ordVal_range` | `nfValue_iff_C`（`Complete.lean`） |
| 構成的な整列性 | `wellFounded_NFLt`・`lt_strictTotal_NF`（`Unconditional.lean`） | `wellFounded_lt`（`Complete.lean`） |
| 二つの意味論は一致する | — | `val_lt_iff_ordVal_lt`・`closure_iso_orderType`（`Agree.lean`） |

「—」の欄は主張そのものが片方の意味論の言葉で書かれているもの（`Ξ_n(α)` が正則であることや (5.6)・(5.7)
は崩壊関数の値についての主張で、記法系の言葉では `cmp` の定義の一部になる）。

### 証明していないこと

設計の §5「まだ確かめていないこと」の 1 つ目（有効性の制限で Compact より強さを失わないか）について、設計で
挙げた根拠は `Design.lean` で示した：`ρ < π = Ξ_k(γ)` なら Rathjen 型の条件 `π ∈ C(α,ρ)` は
`γ < α ∧ γ ∈ C(α,ρ)` と同値（`Xi_mem_C_iff`）。特に `α ≤ γ` なら Rathjen 型の `Ψ_π(α)` にも候補がなく
（`rathjen_no_candidate`）、この体系の `Ψ_π(α)` は Rathjen 型の条件を満たす（`Psi_rathjen_condition`）。
つまり有効性の制限は Rathjen 型の条件が課す制限と同じもの。

残る次の 2 つは **Rathjen 型の Ψ で作った別の体系との強さの比較**で、この体系自身の性質ではないので証明して
いない（形式化には Rathjen 型の体系をここに持ち込み、二つの閉包 `C(Λ,0)` が一致することを示す必要がある）。

* 体系全体として、有効性の制限で Rathjen 型より弱くならないか（上の根拠は 1 つの崩壊ごとの比較）
* Rathjen 型から Buchholz 型に替えても体系全体の到達点が変わらないか

同じく、強さの見積もり（KPM の順序数が `Ψ_{Ω_1}(M_1^+)` のあたりに現れる）も証明していない。これは KPM の
証明論的順序数解析を要する主張で、設計でも「要検証」としていた。

手本にした Compact（`claude/additive-lean-veblen-nf-58eded`）が証明したのも、比較の正しさ・標準形の値の集合が
`C(Λ,0)` と一致すること・標準形の一意性・構成的な整列性の 4 つで、強さの比較は扱っていない。Compact の意味論の
定理も `[Setting]`（加えて `StationaryHyp`）の下で述べられ、同じ `Ordinal.lean` の `least`（`Classical.choose`）を
使う。この体系はその 4 つに加えて基本列を、仮定なしの形と `Setting` の下の形の両方で示している（`Setting` 以外の
仮定は使わない）。

### `Setting` と `Classical.choice` を使う理由

* 設計では最初から `M n` を「`Setting` で与える弱 Mahlo 基数の増加列の第 `n` 項」と定めている。崩壊関数
  `Ψ`・`Ξ` はこの列の上の関数なので、その値についての定理は `Setting` を引数にとる形になる。`setting_iff` が
  示すとおり `Setting` は弱 Mahlo 基数の狭義増加列そのもので、弱 Mahlo 基数の存在は Lean では証明できない
  （無矛盾性の強さが足りない）。元論文も、弱 Mahlo 基数の存在を仮定した集合論の中で崩壊関数を定義している。
* 設計では `Ψ_π(α) := min{η < π : ⋯}`・`Ξ_n(α) := min(⋯)` と、崩壊関数を順序数の集合の最小元で定める。
  `em_of_exists_min`（`Design.lean`、公理は `propext` だけ）は、順序数の最小元の原理から排中律が出ることを示す。
  Lean で排中律を得る手段は `Classical.choice` だけなので、崩壊関数を値として持つ意味論は `Classical.choice` を
  避けられない。
* 記法系についての主張（比較・標準形・整礎性・基本列・順序型による値）は、全て仮定なし・`Classical.choice`
  なしで示してある。`Setting` の下の定理は、その値が崩壊関数の値と一致することを述べる（`closure_iso_orderType`）。


## 構文的な整列性証明の構成

Compact リポジトリの `Compact/WF` と同じ方法（Rathjen・Arai の区別集合）。

1. `WF/Order.lean`：部分項で閉じた有限集合 `S` に項を大きさの順に加え、新しい項 `t` が `S` を切断する
   （`CutT`）ことを示して、不変条件 `GoodY S`（推移性・反対称性と前線の性質）を保つ。`t = Ψ_π(γ)` の切断性は、
   崩壊先が `π` と異なる `Ψ` の比較が `π` 側の底の条件だけで決まる（Buchholz 型）ので、`q < p < t` の `q` の
   崩壊先が `π` の場合だけを `p` の形で分ければよい。
2. `WF/Wmax.lean`：区別集合 `Dist X`、その合併 `Wmax`。この系では `Ψ` の値が崩壊先にならないので、崩壊先を
   たどる列は `Ψ_ρ(a)`、`ρ`、（`ρ = Ξ_n(p)` なら）`M_n` で終わり、`Good` から `Wmax` が無条件に出る。
   `Ξ_n`・`Ψ_π` の閉包は `M_n^+` 以下の範囲 `WK n` の整礎性と、その中の引数についての帰納法で示す
   （`Ξ_n(a)` の引数の上限 `a ≤ M_n^+` はここで使う）。
3. `WF/Fund.lean`：`b` の部分項の節点 `v` について「`v < Ψ_π(b+1)` なら `v < Ψ_π(b)`」を比較の規則だけで
   示し（`Ψ_π(b)` は `b` の部分項にならない）、`b ∈ C(b, Ψ_π(b))` すなわち `Ψ_π(b)` が標準形であることを得る。
   あとは `Ω` の不動点 `X < Ψ_{Ω_d}(·) ⟺ X < d` などの順序の性質から、`Ψ_π(b+1)` 未満の主要項が
   `Ψ_π(b)` 以下であることが出て、基本列の性質になる。

## 基本列（`Mahlo/FS`）

標準形の型 `NF` の上に、`Mahlo/FS/Class.lean` の `FS` クラス（`dom`・`fund` と 0・後者・`ω`・正則項 `σ` の
場合の公理、`ω` 型の Bachmann 性）の基本列を定義した。構成は Compact リポジトリの
`claude/amazing-margulis-20d202`（`Compact/FS`）を、この系（Mahlo 添字なし・Buchholz 型の `Ψ`・`Ξ_n(0)` あり）
に合わせて移したもの。

### 定義（`Mahlo/FS/Seq.lean`）

* 和は最後の加数で決まる：`(a + s)[ξ] = a ⊕ s[ξ]`。
* 正則項 `σ` は `σ[ξ] = base σ ⊕ ξ`（共終数 `σ`）。始点は `Ω_c ↦ Ψ_{Ω_c}(0)`（`Ω_0 ↦ 1`、`Ω_{c+1} ↦ Ω_c·ω`）、
  `M_n ↦ M_{n-1}`、`Ξ_n(d) ↦ Ψ_{Ξ_n(d)}(d+1)`。
* `Ω_c`（`c` 極限）は `Ω_c[ξ] = Ω_{c[ξ]+1}`（共終数は `c` と同じ）。
* 崩壊 `Ψ_π(X)`：
  - `X = 0`：`Ψ_{Ω_0}(0) = 1` は後者、`Ψ_{Ω_{c+1}}(0)[n] = Ω_c·(n+2)`。
  - `X = X' + 1`、`π = Ω_c`：`Ψ_π(X')·(n+2)`。
  - `X = X' + 1`、`π = Ξ_m(d)`：種 `p = Ψ_π(X')` の上の、`Ξ_m(ξ)`（`ξ < d`）と `Ω` についての閉包（`famSeq`）。
    `d < M_m` なら `p` の上の `Ω` の塔、`d ≥ M_m` なら `Ξ_m` の反復（`p, Ξ_m(p), Ξ_m(Ξ_m(p)), …` など）。
    `X' = d`（底）なら種は目標 `π` の前線の最大の節点。
  - 極限 `X`：最後の加数 `R` の近似 `Ψ_π(pre ⊕ (c ⊕ R[ν]))`（`c` は引数の下限 `d < ·` のための調整）。`R` の
    共終数が `π` 未満の正則項 `σ` なら共終数 `σ`、`π` 以上なら添字の列 `γ` で対角化する：
    `σ = π` なら値そのもの（`γ_{k+1} = t[k]`）、`σ` が `π` 以外の崩壊先なら `σ` への崩壊の塔
    `γ_{k+1} = Ψ_σ(pre ⊕ R[γ_k])`、ただし `Ψ_σ(X) < Ψ_π(X)` なら `σ` の族の閉包（`famSeq`、種は目標の前線の最大の
    節点）で、添字の列の共終数（`ω` か正則項）をそのまま `t` の共終数にする（`iapp`）。`σ = M_m` なら `Ξ_m` の塔
    （始点は目標の前線の中の閉じた点の最大のもの）、`M_m⁺` を越える引数は仮想的な崩壊 `virtK`。

`·(n+2)` と始点 `Ψ_{Ω_c}(0)` は、証明に使う「狭義の隙間」（`t` の真の部分項で `t` 未満のものは全ての `t[n]`
未満）を成り立たせるため（`·(n+1)` だと `ω[0] = 1` が `ω` の真の部分項 `1` に等しくなる）。

### 計算量

`cmp`・`inC` は定義どおりに計算すると入れ子の深さについて指数的な時間がかかるので、メモ化版
（`Mahlo/FS/Memo.lean`）を作り、元の定義と一致することを証明して `@[csimp]` で置き換えた。呼び出される組は
入力の部分項とそこから作る項だけなので多項式個。基本列は `info` が項を下から一度だけたどって各節点の列の
記述（`SeqD`）を作り、`t[n]` は記述の木を下るだけ（対角化の添字は `n` 回の反復）で計算する。

`lake exe fstime` の実測：`t[n]` の大きさは `n` に比例し、`n = 128` でも数ミリ秒以内。降下列
`t, t[2], t[2][2], …` をたどって項が数万〜10 万の大きさになると、時間は大きさのおよそ 3〜4 乗で伸びる
（大きさ 3 万で 1 秒前後、10 万で数十秒〜数分）。

### 検査（`FSTest.lean`、`lake exe fstest`）

標準形の標本の各項について FS の全ての性質（基本列の項が標準形・元の項未満・単調・共終、`ω` 型の Bachmann 性
`t[n] < b < t ⇒ t[n] ≤ b[0]`）を標本の中で確かめる。

* 大きさ 7 以下の標準形 2397 個（`lake exe fstest 7`）：反例なし。
* 手で選んだ種の項とその基本列・部分項、大きさ 6 以下の標準形からなる標本 3126 個（`lake exe fstest seeds 6 2`）：
  反例なし。
* 上の標本の項 `u` に `Ω_u`・`Ω_{u+1}`・`Ξ_1(u)`・`Ξ_2(u)`・`Ψ_ρ(u)` をかぶせた項と、崩壊 `Ψ_π(pre + R)` の
  すぐ下の項 `Ψ_π(pre ⊕ R[n])`（とそれにかぶせた項）を加えた標本 42734 個（`lake exe fstest wrap 5 1`）：反例なし。
* 大きな崩壊先・引数を組み合わせた崩壊 `Ψ_π(X)`・`Ψ_π(X+1)` の標本約 184 万個について、列の項が標準形・元の項
  未満・単調であること（`lake exe fstest probe 3 1`）：反例なし。
* 同じ標本で、証明に使う不変量（隙間、正則型の `ξ ≤ t[ξ]`・始点以上・`lbK`・`lbS`）（`lake exe fstest probeInv`）：
  反例なし。
* 標本の中の Bachmann 性の検査では反例は出なかったが、標本に入らない大きさの `b` で反例がある
  （`lake exe fstest probeBachCE2`、`BachCE.lean`。下の「Bachmann 性は今の定義では成り立たない」）。

見つかった誤り：

* 最初の版は `Ψ_{Ξ_1(Ξ_1(M_1))}(M_1)` で共終性が破れていた（`M_1` への対角化の塔を 0 から始めると閉じた点
  `Ξ_1(M_1)` を越えられない）。Compact と同じく塔の始点を目標の前線の中の閉じた点にして直した。
* `Ψ_{Ξ_m(d)}(X'+1)` の列を常に `p = Ψ_{Ξ_m(d)}(X')` の上の `Ω` の塔にしていたのは、`d ≥ M_m` で誤り
  （`Ψ_{Ξ_1(M_1)}(M_1+2)` 未満に `Ξ_1(Ψ_{Ξ_1(M_1)}(M_1+1))` があり、塔はそれを越えない）。目標の族の閉包
  （`famSeq`）に直した。`fstest 7`・`seeds` の標本にはこの形の項がなく、`wrap` の標本で見つかる（旧定義で 12 件）。
* 外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` のとき、添字の族の閉包の共終数が正則項になる場合がある
  （`E = Ψ_{Ω_{M_1+1}}(Ω_1)`、`σ = Ξ_1(E)`、`X = E + σ`、`π = Ξ_1(Ψ_σ(X)+1)` の `Ψ_π(X)` では閉包の共終数が
  `Ω_1`）。添字の列を常に `ω` 型として扱っていたので、`t[n]` が全て等しくなっていた。添字の列の共終数を
  そのまま `t` の共終数にするよう直した（`iapp`）。

### 証明したこと（公理は `propext`・`Quot.sound` だけ）

列の性質は、FS の公理に要る性質（`NatProps`・`BigProps`：標準形・減少・単調・共終）に、崩壊の列を部分項の列から
組み立てるための不変量を加えた `Inv`（`Inv.lean`）として、項の大きさについての帰納法で示す。

* 上界 `ub`：`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)`（`d` は切断でよい。近似 `Ψ_π(A_n)` の標準形の条件
  `A_n ∈ C(A_n, Ψ_π(A_n))` を `d = Ψ_π(A_n)` に使って示すため）。
* 隙間 `gap`：`t` の真の部分項で `t` 未満のものは `t[n]` 未満（近似の引数 `A_n` が `X` の部分項を越えるため）。

| 内容 | ファイル |
|---|---|
| メモ化した `cmp`・`inC` が元の定義と一致する（`cmp_eq_cmpFast`・`inC_eq_inCFast`） | `Memo.lean` |
| `NF` の整列順序（`Well_Order NF`） | `Order.lean` |
| 和・自然な和・倍の標準形と大小、`C(g, d)` への所属 | `Arith.lean`・`CLem.lean` |
| 共終数が 0 ⟺ 項が 0、共終数が後者 ⟺ 最後の加数が `1`、自然数の公理 | `Dom.lean` |
| 標準形と分かる前の崩壊の候補 `Ψ_π(A)` との比較：移し替え、`b < Ψ_π(A) ⇒ b < π`、切断（`below_cut`） | `Below.lean` |
| 和・正則項・`Ω_c`（`c` 極限）の列の不変量。崩壊の場合（`PsiInv`）から全ての標準形の不変量（`inv_all`） | `Inv.lean` |
| `Ψ_{Ω_c}(0)` と `Ψ_{Ω_d}(X'+1)` の列（`B·(n+2)`） | `PsiMul.lean` |
| 極限 `X` の素の近似（`R` の列が `ω` 型、または共終数 `σ < π`。調整 `c` を含む） | `Split.lean`・`PsiLim.lean` |
| `Ψ_{Ξ_m(q)}(X'+1)`（`q < M_m`、`q < X'`）の列：`p` の上の `Ω` の塔 | `PsiXi.lean` |
| 共終性の道具：閉じた点 `Cl`、崩壊への移し替えの一歩（`psi_step`・`coll_step`）、成分による帰納法（`cof_nat`） | `Clo.lean` |
| 対角化：添字の列による近似（`natInv_psi_idx`）、目標そのものへの対角化（`inv_psi_diag_in`） | `PsiDiag.lean` |
| 外に足す型の塔（`Ψ_π(X) < Ψ_σ(X)` のとき、`γ_{k+1} = Ψ_σ(pre ⊕ R[γ_k])`） | `PsiOut.lean` |
| 対角化の場合分け（`psiDiagInv_of`） | `PsiAll.lean` |
| `Ξ_m` の反復の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])` の閉包性（`xi_tower_hull`） | `XiIter.lean` |
| 閉じた点の探索（`maxCl`・`frCl`・`kStart`）の仕様、閉じた点が始点以下の項（`CF`） | `KCl.lean` |
| `M_m` への対角化で近似が `M_m⁺` 未満（`canonK`）：目標が塔の下にあること・共終性 | `PsiK.lean` |
| 自然な和の可換性、仮想的な崩壊 `virtK`（`M_m` 未満の全ての標準形がその下にある：`virt_all`） | `Virt.lean` |
| `M_m` への対角化で近似が `M_m⁺` 以上（`kOld`）、`M_m` への対角化全体（`psiDiagM_proof`） | `PsiKO.lean` |
| 族の閉包 `mahloVK` の列の仕様（`ω` 型 `FamNat`・正則項型 `FamBig`）、種の仮定 `SeedHyp` | `FamSeq.lean`・`FamApp.lean`・`FamVK.lean`・`FamBig.lean` |
| `Ψ_{Ξ_m(q)}(X'+1)` で `q < X'`（種 `Ψ_{Ξ_m(q)}(X')` の上の族の閉包） | `XiSucc.lean` |
| `Ψ_{Ξ_m(q)}(q+1)`（底：種は目標の前線の最大元、`psiXiSuccFloor_proof`） | `XiFloor.lean` |
| 外に足す型で `Ψ_σ(X) ≤ Ψ_π(X)` の場合（添字は `σ = Ξ_k(e)` の族の閉包、`psiDiagFam_proof`） | `PsiFam.lean` |
| 全ての標準形の列の不変量（`inv_of`）と、Bachmann 性から `FS NF`（`fsNF`） | `Inst.lean` |

正則型の列の不変量 `BigInv` には、共終性を添字で表した `lclo`（`x < t` で `x` の `σ` 未満の極大部分項が添字 `ξ`
未満なら `x < t[ξ]`）と、`M_m` への対角化で使う下界 `lbK`・`lbS`（共終数 `M_m` で `t > M_m`（`t > M_m⁺`）なら
`t[ξ] ≥ M_m`（`t[ξ] ≥ M_m⁺`））を持たせている。

### 外に足す型で `Ψ_σ(X) ≤ Ψ_π(X)` の場合（`PsiFam.lean`）

`t = Ψ_π(X)`、`X = pre + R`、`R` の共終数 `σ` が `π` より大きく、`t < Ψ_σ(X)` でない場合。`T = Ψ_σ(X)` は
標準形とは限らない（`lake exe fstest probeCE` の例：`σ = Ξ_1(0)`、`π = Ω_{P+1}`、`P = Ψ_σ(M_1)` で `T` は標準形で
ない）ので、`σ` の始点 `B = Ψ_σ(e+1)`（標準形）を使う。

* `σ = Ξ_k(e)`（`lev π = k`）で、`B` は `π` の底の条件を満たさない（`a2_shape`）。したがって `B` は全ての
  `Ψ_π(A)` 未満で、目標 `π` の前線の最大元 `P0` は `B` 以上（`a2_P0`）。
* 添字は `P0` の上の `Ξ_k(ξ)`（`ξ < e`）の閉包。`e` の加数で `σ` 未満のものは `B` 未満なので、`B ≤ P0 < σ` から
  種の仮定 `SeedHyp` が出る（`seedHyp_base`）。
* 共終性：`x = Ψ_π(a) < t` の `a` の `σ` 未満の極大部分項は `C(a, x)` に入り、添字の列の下にある
  （`hull_nat`・`hull_big`：`x` 未満なら `π` の下、`x` 以上なら成分に分けて族の閉包・`B` で押さえる）。
* 2 点の上界 `ub2` の仮定「`σ` の始点が `C(g, d)` に入る」は「`σ` の始点が添字以下」でもよいように弱めた
  （`BigInv.ub2`・`FamBig.ub2`）。

### Bachmann 性は今の定義では成り立たない

列の不変量（`inv_of`：標準形・減少・単調・共終など、Bachmann 以外の全ての FS の性質）は仮定なしで示して
ある。`fsNF` が受け取る仮定 `BachHyp`（`ω` 型の Bachmann 性）は、今の基本列の定義では**偽**である
（`BachCE.lean` の `not_bachHyp : ¬ BachHyp`、`native_decide` による計算。`lake exe fstest probeBachCE2` でも
同じ値を出力する）。

* 反例：`σ = Ξ_1(0)`、`P = Ψ_σ(M_1)`、`S1 = Ψ_{Ξ_1(σ+1)}(σ + P + 2)`、`c = Ψ_{Ω_{P+1}}(5)`、`π = Ω_{c+1}`、
  `t = Ψ_π(S1 + σ)`。外に足す型で `Ψ_σ(X) ≤ t` の対角化（`PsiFam.lean`）で、添字は種 `c`（`π` の前線の最大元）
  の上の `Ω` の塔 `Ω_{c+1}, Ω_{Ω_{c+1}+1}, …` になり、`t[n] = Ψ_π(S1 + y_n)`。`d = Ψ_{Ω_{P+1}}(ω)` について
  `b = Ψ_π(S1 + Ω_d)` は `t[0] < b < t` だが、`d[0] = Ψ_{Ω_{P+1}}(2) < c` なので `b[0] < t[0]`。
* 原因：`Ω` について閉じていない種 `c` の上の塔では、区間 `(c, Ω_{c+1})` に `d[0] < c` となる `d` があり、
  `Ω_d` が塔の隣り合う項の間に入る。直すには、族の閉包の塔の始点を（種より上の）`Ω` について閉じた点など、
  Bachmann 性を壊さない点にする必要がある（底の場合 `XiFloor.lean` の塔も、種が前線の元なので同じ点検が要る）。

`Bach.lean` は Bachmann 性を、隣り合う列の項の区間の下界 `LBI (t[n]) (t[n+1])`（区間 `(t[n], t[n+1]]` の
全ての `b` で `t[n] ≤ b[0]`）に帰着させる（`bachHyp_of_ladder`）。基本列を直した後の証明はこの形で進める。

## ファイル

* `Mahlo/Ordinal.lean`：順序数（Compact から変更なしでコピー）
* `Mahlo/Setting.lean`：基数の設定と崩壊関数の定義
* `Mahlo/Basic.lean`・`Mahlo/Compare.lean`・`Mahlo/Gen.lean`：崩壊関数の性質
* `Mahlo/Notation.lean`：記法系（項、`cmp`、`inC`、`baseOf`、`isNF`）
* `Mahlo/Good.lean`・`Mahlo/Correct.lean`・`Mahlo/NF.lean`：記法系の正しさ
* `Mahlo/Succ.lean`：後続基数への崩壊の基本列
* `Mahlo/Complete.lean`：等号の定理、弱 Mahlo 基数の列からの結論
* `Mahlo/WF/Syntax.lean`・`Mahlo/WF/Order.lean`・`Mahlo/WF/Wmax.lean`：構文的な順序の性質と整列性
* `Mahlo/WF/Fund.lean`：後続基数への崩壊の基本列の構文的な証明
* `Mahlo/Unconditional.lean`：仮定なしの結論と順序型による値
* `Mahlo/Agree.lean`：二つの意味論の一致
* `Mahlo/Design.lean`：設計の比較規則の仮定なしの形、到達不能基数への崩壊の基本列、古典論理が要る理由
* `Mahlo/FS/Class.lean`：基本列の公理（`Well_Order`・`Cof`・`FS`）
* `Mahlo/FS/Memo.lean`：`cmp`・`inC` のメモ化版（多項式時間）と一致の証明
* `Mahlo/FS/Def.lean`・`Mahlo/FS/Seq.lean`：基本列の定義（`dom`・`fund`）
* `Mahlo/FS/Arith.lean`・`Mahlo/FS/CLem.lean`：和・自然な和・倍の性質（Compact から移植）
* `Mahlo/FS/Dom.lean`：共終数の分類、0・後者・自然数の公理
* `Mahlo/FS/Order.lean`：`NF` の整列順序
* `Mahlo/FS/Props.lean`：FS の公理に要る列の性質（`NatProps`・`BigProps`）と、構造的な場合
* `Mahlo/FS/Below.lean`：崩壊の候補 `Ψ_π(A)` との比較（移し替え・切断）
* `Mahlo/FS/Base.lean`：`Ξ_n(d)` の列の始点の標準形
* `Mahlo/FS/Inv.lean`：列の不変量（上界・隙間）と構造的な場合、崩壊の場合への帰着
* `Mahlo/FS/PsiMul.lean`：`Ψ_{Ω_c}(0)`・`Ψ_{Ω_d}(X'+1)` の列
* `Mahlo/FS/Split.lean`・`Mahlo/FS/PsiLim.lean`：極限 `X` の素の近似の列
* `Mahlo/FS/PsiXi.lean`：`Ψ_{Ξ_m(q)}(X'+1)`（`q < M_m`）の列（`Ω` の塔）
* `Mahlo/FS/Clo.lean`：共終性の道具（閉じた点、移し替えの一歩、成分による帰納法）
* `Mahlo/FS/PsiDiag.lean`・`Mahlo/FS/PsiOut.lean`・`Mahlo/FS/PsiAll.lean`：対角化（目標そのもの・外に足す型の塔）
  と場合分け
* `Mahlo/FS/XiIter.lean`・`Mahlo/FS/KCl.lean`・`Mahlo/FS/PsiK.lean`・`Mahlo/FS/Virt.lean`・`Mahlo/FS/PsiKO.lean`：
  `M_m` への対角化
* `Mahlo/FS/XiFam.lean`・`Mahlo/FS/FamSeq.lean`・`Mahlo/FS/FamApp.lean`・`Mahlo/FS/FamVK.lean`・
  `Mahlo/FS/FamBig.lean`：族の閉包 `mahloVK` の列の仕様
* `Mahlo/FS/XiSucc.lean`・`Mahlo/FS/XiFloor.lean`：`Ξ_m(q)` への崩壊の後者（族の閉包）
* `Mahlo/FS/PsiFam.lean`：外に足す型で `Ψ_σ(X) ≤ Ψ_π(X)` の対角化（族の閉包を添字にする）
* `Mahlo/FS/Inst.lean`：全ての標準形の列の不変量と、`FS NF`（Bachmann 性を仮定）
* `Mahlo/FS/Bach.lean`：Bachmann 性の梯子（区間の下界）への帰着
* `Mahlo/FS/BachCE.lean`：今の基本列での Bachmann 性の反例（`native_decide`）
* `FSTest.lean`（`lake exe fstest`）：標本での検査（総当たり・種・かぶせた項）、`FSTime.lean`（`lake exe fstime`）：計時
