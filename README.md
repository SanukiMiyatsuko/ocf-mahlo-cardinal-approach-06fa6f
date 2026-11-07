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
