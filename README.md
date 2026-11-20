# Mahlo

M. Rathjen, *Ordinal notations based on a weakly Mahlo cardinal*（Arch. Math. Logic 29, 1990）の記法系から
Veblen 関数を抜き、閉包を加法だけにした順序数崩壊関数（OCF）と、その記法系の Lean 4 による形式化。崩壊関数
`Ψ` は Buchholz 型（底の条件が崩壊先だけで決まる）。構成は Compact リポジトリ（弱コンパクト版）にならう。
mathlib には依存しない。

主な結果：

* **記法系**：6 種類の構成子からなる項 `Tm`、計算可能な比較 `cmp`・所属 `inC`・標準形の判定 `isNF`
  （停止性を証明した全域関数）。
* **正しさと完全性**（弱 Mahlo 基数の増加列 `Setting` の下）：標準形の上で `cmp` は崩壊関数による値の比較と
  一致し（`cmp_correct_of_isNF`）、標準形の値の集合はちょうど崩壊関数の閉包 `C(Λ, 0)`（`nfValue_iff_C`）。
* **構成的な整列性**（仮定なし）：標準形全体の上の `<` は整礎（`wellFounded_isNF`）。
* **仮定なしの値**：整列順序の順序型による値 `ordVal`。どの `Setting` でも崩壊関数による値と同じ順序を与える
  （`closure_iso_orderType`）。
* **基本列**（仮定なし）：標準形の型 `NF` の上の基本列 `fsNF : FS NF`。`ω` 型の Bachmann 性を含む基本列の
  公理を全て満たす（`bachHyp_proof`）。
* **可算な部分**：可算な標準形全体は、可算な極限の始点 `Ψ_{Ω_0}(M_{n+1})` から基本列の一歩の推移閉包で
  到達できる元全体に等しい（`countable_eq_reach`・`NOT_eq`）。

記法系・構文的な証明・基本列の定理の公理は `propext`・`Quot.sound` だけ（`Classical.choice` も大基数の仮定も
使わない）。崩壊関数を値として持つ意味論の定理は `Classical.choice` を使う（理由は「`Setting` と
`Classical.choice`」）。`sorry` は無い。主な定理の公理は `#guard_msgs` でビルドのたびに検査している。

## ビルドと実行

* Lean `v4.35.0`（`lean-toolchain`）。依存パッケージは無い。
* `lake build`：ライブラリ全体（`Mahlo.lean` が全てのファイルを読み込む）と既定の実行ファイル `mahlo` を作る。
* `lake exe mahlo`：いくつかの項（`1`・`ω`・`ε_0`・`Ω_0`・`Ξ_1(0)`・`M_1`・`M_1^+` など）とその `isNF` を表示する。
* 検査用の実行ファイル `fstest`・`fstime`・`fsprobe`（「検査と計時」）。

名前空間：崩壊関数の意味論は `OCF.Mahlo`、記法系と構文的な証明は `MahloOCF`、基本列は `MahloOCF.FS`。

## 体系

### 基数と崩壊関数（`Mahlo/Setting.lean`）

* `M_1 < M_2 < ⋯` は弱 Mahlo 基数（非可算正則で、正則基数全体が定常）の増加列（`Setting`）。`K_0 = 0`、
  `K_{n+1} = M_{n+1}`、`Λ = sup K_n`。
* `Ω_x = ℵ_{1+x}`：非可算基数全体の数え上げ（`Ω_0 = ℵ_1`）。`M_m^+ = Ω_{M_m + 1}`。
* 段 `α` についての同時再帰で次を定める。
  - `C(α, β)`：`β ∪ {K_m}` を `+`、`Ω`（引数 `< Λ`）、`Ξ_m(ξ)`（`ξ < α`）、`Ψ_π(δ)`（`δ < α`、`π` 正則、
    `Ψ_π(δ) < π` で `δ ∈ C(δ, Ψ_π(δ))`）で閉じたもの。
  - `M^α = {ρ ∈ Reg : C(α, ρ) ∩ K(ρ) ⊆ ρ ∧ α ∈ C(α, ρ)}`（定常性の条件は無い）。
  - `Ξ_m(α) = min((M^α ∩ (K_{m-1}, K_m)) ∪ {K_m})`（`M_m` への Mahlo 崩壊）。
  - `Ψ_π(α) = min({η < π : Base_π(η) ∧ C(α, η) ∩ π ⊆ η} ∪ {π})`（Buchholz 型の崩壊）。底の条件は崩壊先だけで
    決まる：`Base_{Ω_0}(η) ⟺ 0 < η`、`Base_{Ω_{ζ+1}}(η) ⟺ Ω_ζ < η`、
    `Base_{Ξ_m(δ)}(η) ⟺ K_{m-1} < η ∧ δ ∈ C(δ, η)`（`δ < α` のときだけ有効）。

### 記法系（`Mahlo/Notation.lean`）

* 項は `zero`・`M n`・`plus a b`・`Om a`・`Xi n a`・`Psi pi a` の 6 種類。`1` は定数でなく
  `one := Ψ_{Ω_0}(0)`。`M_n^+` は `succM n = Ω_{M_n + 1}`。
* 標準形 `isNF`：和 `a + b` は主要項の非増加な並び、`Ω_a` は `a` が `Ω` の不動点でないとき、`Ξ_n(a)` は
  `n ≥ 1`・`a ≤ M_n^+`・`a ∈ C(a, M_n)`、`Ψ_π(a)` は `π` が正則な項（`Ω_0`・`Ω_{c+1}`・`Ξ_n(d)`）で
  `a ∈ C(a, Ψ_π(a))`、`π = Ξ_n(d)` なら `d < a`。
* 比較 `cmp`：和は辞書式、和でない項は階（`M_{n-1} ≤ x < M_n` となる `n`）で比べ、同じ階では `Ξ` どうしは
  Lemma 4.14、`Ψ` と `Ξ`・異なる崩壊先の `Ψ` どうしは分離補題から「崩壊先 `σ` の底の条件を満たすか」（`baseOf`）で、
  同じ崩壊先の `Ψ` どうしは引数で比べる。`C(α, β)` への所属の判定は `inC`。
* `cmp`・`inC`・`baseOf`・`isNF` は停止性を証明した全域関数（測度は `(引数の大きさの最大, 大きさの和, 段)` の
  辞書式順序）。

## 主な定理

### 意味論（`Setting` の下）

| 定理 | ファイル | 内容 |
|---|---|---|
| `Xi_lt` | `Basic.lean` | `α ∈ C(α, M_m)` なら `Ξ_m(α) < M_m`（Mahlo 性） |
| `Psi_Om_zero_zero` | `Basic.lean` | `Ψ_{Ω_0}(0) = 1` |
| `Xi_lt_Xi_iff` | `Compare.lean` | Lemma 4.14（`Ξ` どうしの比較） |
| `sep` | `Compare.lean` | 分離補題：`κ < π` が崩壊先なら `Ψ_π(β) ≤ κ` のとき `¬ Base_κ(Ψ_π(β))` |
| `Psi_lt_target_iff` ほか | `Compare.lean` | `Ψ` と崩壊先・`Ψ` どうしの比較、`Ψ` の単射性 |
| `cmp_correct`・`inC_correct`・`baseOf_correct` | `Correct.lean` | `Good` な項について比較・`C` への所属・底の条件の判定が正しい |
| `isNF_iff_good` | `NF.lean` | 計算可能な `isNF` は意味論的な標準形 `Good` のちょうどの判定 |
| `cmp_correct_of_isNF`・`val_inj_of_isNF` | `NF.lean` | 標準形の上で `cmp` は値の比較と一致し、標準形は一意 |
| `Psi_succ_fs`・`fs_psi_succ` | `Succ.lean` | `π = Ω_0, Ω_{ζ+1}` なら `Ψ_π(β+1) = sup_n Ψ_π(β)·(n+1)`、記法系での基本列 |
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
| `wellFounded_NFLt`・`lt_strictTotal_NF`・`cmp_eq_iff_NF`・`cmp_swap_NF`・`fs_psi_succ_NF` | `Unconditional.lean` | `Complete.lean`・`Succ.lean` の記法系についての主張を仮定なしで |

### 仮定なしの順序数への値（`Unconditional.lean`）

整礎な狭義全順序から、標準形の値を始切片の順序型 `ordVal a`（`nfWellOrder` の `a` 未満の部分の型）で定める。

| 定理 | 内容 | 対応する意味論の定理 |
|---|---|---|
| `cmp_ordVal` | `cmp` は値の比較と一致する | `cmp_correct_of_isNF` |
| `ordVal_inj` | 値が等しければ標準形も等しい | `val_inj_of_isNF` |
| `ordVal_range` | 値の集合はちょうど記法系の順序型 `nfOrderType` 未満の順序数 | `nfValue_iff_C` |
| `ordVal_fs` | `Ψ_π(b+1)` の値は基本列 `Ψ_π(b)·(n+1)` の値の上限 | `Psi_succ_fs` |

### 二つの意味論の一致（`Agree.lean`）

| 定理 | 内容 |
|---|---|
| `setting_iff` | `Setting` は弱 Mahlo 基数の狭義増加列 `M_1 < M_2 < ⋯` そのもの |
| `val_lt_iff_ordVal_lt`・`val_eq_iff_ordVal_eq` | どの `Setting` でも、崩壊関数による値 `val` と仮定なしの値 `ordVal` は標準形に同じ順序を与える |
| `closure_iso_orderType` | どの `Setting` でも、`C(Λ, 0)` は順序を保って `nfOrderType` 未満の順序数と一対一に対応する |

### 設計上の主張と定理の対応

「仮定なし」の列は大基数の仮定を使わず、公理も `propext`・`Quot.sound` だけの定理。「`Setting` の下」の列は
崩壊関数 `Ψ`・`Ξ` の値についての定理で、どの `Setting` についても成り立つ。

| 主張 | 仮定なし | `Setting` の下 |
|---|---|---|
| 構成子は `zero`・`plus`・`M n`・`Om`・`Xi`・`Psi` の 6 個で、`1` は定義 `Ψ_{Ω_0}(0)` | `Tm`・`one`（`Notation.lean`） | — |
| `1 = Ψ_{Ω_0}(0)`（`C(0,1) ∩ ℵ_1 = {0}`） | `ordVal_lt_one`・`not_ordVal_lt_zero`（`Design.lean`） | `Psi_Om_zero_zero`（`Basic.lean`） |
| `Ξ_n(α)` は `M_n` 未満で正則 | — | `Xi_lt`・`Xi_mem`・`XiGood`（`Basic.lean`） |
| Lemma 4.14（`Ξ` どうしの比較） | `ordVal_xi_xi`（`Design.lean`） | `Xi_lt_Xi_iff`・`Xi_inj`（`Compare.lean`） |
| (5.7) `C(β, Ψ_π(β)) ∩ π ⊆ Ψ_π(β)` | — | `Psi_spec`（`Setting.lean`） |
| (5.6) 分離補題 | — | `sep`（`Compare.lean`） |
| 同じ崩壊先：`Ψ_π(a) < Ψ_π(b) ⟺ a < b` | `ordVal_psi_same`（`Design.lean`） | `Psi_lt_Psi_same`（`Compare.lean`） |
| `σ < π`：`Ψ_π(a) < Ψ_σ(b) ⟺ ¬Base_σ(Ψ_π(a))` | `ordVal_psi_psi_of_target_lt`・`ordVal_psi_psi_of_lt_target`（`Design.lean`） | `Psi_lt_Psi_iff_lt`・`Psi_lt_Psi_iff_gt`（`Compare.lean`） |
| `κ < π` が正則：`Ψ_π(a) < κ ⟺ ¬Base_κ(Ψ_π(a))` | `ordVal_psi_xi_of_lt_target`（`Design.lean`） | `Psi_lt_target_iff`（`Compare.lean`） |
| 比較は `inC`・`baseOf` の判定に帰着し、計算できる | `cmp`・`inC`・`baseOf`・`isNF`（`Notation.lean`）と `cmp_ordVal` | `cmp_correct_of_isNF`（`NF.lean`） |
| 標準形の条件（`π = Ξ_n(d)` なら `d < a`、`a ∈ C(a, Ψ_π(a))`）と一意性 | `cmp_eq_iff_NF`・`ordVal_inj` | `isNF_iff_good`・`val_inj_of_isNF`（`NF.lean`） |
| 後続基数への崩壊 `Ψ_π(β+1)[n] = Ψ_π(β)·(n+1)` | `fs_psi_succ_NF`・`ordVal_fs`（`Unconditional.lean`） | `Psi_succ_fs`・`fs_psi_succ`（`Succ.lean`） |
| 到達不能基数への崩壊では `·ω` にできない（`Ω` の入れ子が挟まる） | `psi_xi_fs_not_cofinal`（`Design.lean`） | — |
| 有効性の制限は Rathjen 型の条件 `π ∈ C(α,ρ)` と同じ制限 | — | `Xi_mem_C_iff`・`rathjen_no_candidate`・`Psi_rathjen_condition`（`Design.lean`） |
| 完全性：`C(Λ,0)` の元は全て標準形の値 | `ordVal_range` | `nfValue_iff_C`（`Complete.lean`） |
| 構成的な整列性 | `wellFounded_NFLt`・`lt_strictTotal_NF`（`Unconditional.lean`） | `wellFounded_lt`（`Complete.lean`） |
| 二つの意味論は一致する | — | `val_lt_iff_ordVal_lt`・`closure_iso_orderType`（`Agree.lean`） |

「—」の欄は主張そのものが片方の意味論の言葉で書かれているもの（`Ξ_n(α)` が正則であることや (5.6)・(5.7) は
崩壊関数の値についての主張で、記法系の言葉では `cmp` の定義の一部になる）。

### 証明していないこと

`ρ < π = Ξ_k(γ)` なら Rathjen 型の条件 `π ∈ C(α,ρ)` は `γ < α ∧ γ ∈ C(α,ρ)` と同値（`Xi_mem_C_iff`）で、
`α ≤ γ` なら Rathjen 型の `Ψ_π(α)` にも候補がなく（`rathjen_no_candidate`）、この体系の `Ψ_π(α)` は Rathjen 型の
条件を満たす（`Psi_rathjen_condition`）。つまり有効性の制限は、1 つの崩壊ごとには Rathjen 型の条件と同じもの。

次は **Rathjen 型の `Ψ` で作った別の体系との強さの比較**で、この体系自身の性質ではないので証明していない
（形式化には Rathjen 型の体系を持ち込み、二つの閉包 `C(Λ,0)` が一致することを示す必要がある）。

* 体系全体として、有効性の制限で Rathjen 型より弱くならないか
* Rathjen 型から Buchholz 型に替えても体系全体の到達点が変わらないか

強さの見積もり（KPM の順序数が `Ψ_{Ω_1}(M_1^+)` のあたりに現れる）も、KPM の証明論的順序数解析を要する主張で、
証明していない。

### `Setting` と `Classical.choice`

* `M n` は「`Setting` で与える弱 Mahlo 基数の増加列の第 `n` 項」で、崩壊関数 `Ψ`・`Ξ` はこの列の上の関数なので、
  その値についての定理は `Setting` を引数にとる。`setting_iff` が示すとおり `Setting` は弱 Mahlo 基数の狭義増加列
  そのもので、弱 Mahlo 基数の存在は Lean では証明できない（元論文も、その存在を仮定した集合論の中で崩壊関数を
  定義している）。
* 崩壊関数は順序数の集合の最小元で定める。順序数の最小元の原理からは排中律が出る（`em_of_exists_min`、
  `Design.lean`、公理は `propext` だけ）。Lean で排中律を得る手段は `Classical.choice` だけなので、崩壊関数を値と
  して持つ意味論は `Classical.choice` を避けられない。
* 記法系についての主張（比較・標準形・整列性・基本列・順序型による値）は、全て仮定なし・`Classical.choice` なしで
  示してある。`Setting` の下の定理は、その値が崩壊関数の値と一致することを述べる（`closure_iso_orderType`）。

手本にした Compact（`claude/additive-lean-veblen-nf-58eded`）が示したのは、比較の正しさ・標準形の値の集合が
`C(Λ,0)` と一致すること・標準形の一意性・構成的な整列性の 4 つ。この体系はそれに加えて基本列を、仮定なしの形と
`Setting` の下の形の両方で示している（`Setting` 以外の仮定は使わない）。

## 構文的な整列性証明の構成（`Mahlo/WF`）

Compact リポジトリの `Compact/WF` と同じ方法（Rathjen・Arai の区別集合）。

1. `WF/Syntax.lean`・`WF/Order.lean`：部分項で閉じた有限集合 `S` に項を大きさの順に加え、新しい項 `t` が `S` を
   切断する（`CutT`）ことを示して、不変条件 `GoodY S`（推移性・反対称性と前線の性質）を保つ。`t = Ψ_π(γ)` の
   切断性は、崩壊先が `π` と異なる `Ψ` の比較が `π` 側の底の条件だけで決まる（Buchholz 型）ので、`q < p < t` の
   `q` の崩壊先が `π` の場合だけを `p` の形で分ければよい。
2. `WF/Wmax.lean`：区別集合 `Dist X`、その合併 `Wmax`。この系では `Ψ` の値が崩壊先にならないので、崩壊先を
   たどる列は `Ψ_ρ(a)`、`ρ`、（`ρ = Ξ_n(p)` なら）`M_n` で終わり、`Good` から `Wmax` が無条件に出る。`Ξ_n`・`Ψ_π`
   の閉包は `M_n^+` 以下の範囲 `WK n` の整礎性と、その中の引数についての帰納法で示す（`Ξ_n(a)` の引数の上限
   `a ≤ M_n^+` はここで使う）。
3. `WF/Fund.lean`：`b` の部分項の節点 `v` について「`v < Ψ_π(b+1)` なら `v < Ψ_π(b)`」を比較の規則だけで示し
   （`Ψ_π(b)` は `b` の部分項にならない）、`b ∈ C(b, Ψ_π(b))` すなわち `Ψ_π(b)` が標準形であることを得る。
   `Ω` の不動点 `X < Ψ_{Ω_d}(·) ⟺ X < d` などの順序の性質から、`Ψ_π(b+1)` 未満の主要項が `Ψ_π(b)` 以下である
   ことが出て、基本列の性質になる。

## 基本列（`Mahlo/FS`）

標準形の型 `NF := {t : Tm // isNF t = true}`（整列順序は `wellFounded_isNF`）の上に、`FS` クラスの基本列
`fsNF : FS NF`（`Final.lean`）を定義し、全ての公理を仮定なしで示した。構成は Compact リポジトリの
`claude/amazing-margulis-20d202`（`Compact/FS`）を、この系（Mahlo 添字なし・Buchholz 型の `Ψ`・`Ξ_n(0)` あり）に
合わせて移したもの。

### 公理（`Class.lean`）

共終数の型 `Cof` は `zero`・`one`（後者）・`omega`・`big σ`（正則項 `σ`、添字は `σ` 未満の元）。`≤` は
`Well_Order` の `<` から `a < b ∨ a = b` で入れる。

| 場合 | 公理 |
|---|---|
| 自然数 | `ofNat_zero`（`ofNat 0 = Z`）・`ofNat_dom`（`ofNat (n+1)` は後者）・`ofNat_fund`（`ofNat (n+1)[m] = ofNat n`） |
| `0` | `zero_dom`・`zero_unique`（共終数 `0` は `Z` だけ）・`zero_fund`・`zero_least`（`Z ≤ a`） |
| 後者 | `succ_md`（`a[n] < a`）・`succ_cof`（`x < a ⇒ x ≤ a[n]`） |
| `ω` | `omega_lt`・`omega_mono`・`omega_cof`・`omega_bachmann`（`a[n] < b < a ⇒ a[n] ≤ b[0]`） |
| 正則項 `σ` | `big_lt`・`big_mono`・`big_cof`・`big_regular`（`dom σ = .big σ`） |

Compact の公理に加えたのは次の 2 つ。

* `zero_least`：`Z` は最小元。他の公理のもとで「共終数が正則項 `σ` なら `Z < σ`（添字の集合が空でない）」と同値で、
  他の公理からは出ない（`m < Z` で `dom m = .big m` の元 `m` を足したモデルがある）。この系では `Z = 0`（`zero_le`）。
* `big_regular`：共終数は正則（共終数の共終数は自分自身）。この系の共終数は常に正則項 `Ω_0`・`Ω_{c+1}`・`M_n`・`Ξ_n(d)`
  （不変量 `BigInv.σreg`、`isRegY_of_dom_big`）で、その共終数は自分自身（`dom_of_isRegY`）。

共終数が正則項の列の Bachmann 性を `a[ξ] < b < a ⇒ a[ξ] ≤ b[0]` の形で課すことはできない（`a = Ω_0`・`ξ = ω+5`・
`b = ω·2` で `b[0] = ω+2 < a[ξ]`。正則項の列はほぼ恒等なので、どの自然な体系でも破れる）。隣り合う添字の形
`a[ξ] < b < a[ξ+1] ⇒ a[ξ] ≤ b[0]` は標本の検査では反例が無いが、公理には入れていない（添字が `0` か `σ` の始点より
大きい主要項なら、証明に使う強い形 `BInv` から出る。それ以外の添字の場合は未証明）。

### 定義（`Def.lean`・`Seq.lean`）

項 `t` の共終数 `dom t` と、基本列 `fundNat t n`（共終数 `ω`）・`fundBig t ξ`（共終数が正則項）。`fund t ξ` は
共終数に応じてそのどちらか（後者なら直前の項）。

* 和は最後の加数で決まる：`(a + s)[ξ] = a ⊕ s[ξ]`。
* 正則項 `σ` は `σ[ξ] = base σ ⊕ ξ`（共終数 `σ`）。始点 `base σ` は `Ω_c ↦ Ψ_{Ω_c}(0)`（`Ω_0 ↦ 1`、
  `Ω_{c+1} ↦ Ω_c·ω`）、`M_n ↦ M_{n-1}`、`Ξ_n(d) ↦ Ψ_{Ξ_n(d)}(d+1)`。
* `Ω_c`（`c` 極限）は `Ω_c[ξ] = Ω_{c[ξ]+1}`（共終数は `c` と同じ）。
* 崩壊 `Ψ_π(X)`：
  - `X = 0`：`Ψ_{Ω_0}(0) = 1` は後者、`Ψ_{Ω_{c+1}}(0)[n] = Ω_c·(n+2)`。
  - `X = X' + 1`、`π = Ω_c`：`Ψ_π(X')·(n+2)`。
  - `X = X' + 1`、`π = Ξ_m(d)`：種 `p = Ψ_π(X')` の上の、`Ξ_m(ξ)`（`ξ < d`）と `Ω` についての閉包
    （`famSeq`・`mahloVK`）。`d < M_m` なら `p` の上の `Ω` の塔、`d ≥ M_m` なら `d` の `M_m` 以上の加数の近似
    `Ξ_m(pre ⊕ (p # R[ν]))`（`R = M_m` なら `Ξ_m` の反復）。`X' = d`（底）なら種は目標 `π` の前線の最大の節点。
  - 極限 `X = pre + R`：最後の加数 `R` の近似 `Ψ_π(pre ⊕ (c ⊕ R[ν]))`（`c` は引数の下限のための調整：下限が
    `δ = pre ⊕ rt` なら `rt + 1`、そうでなければ `0`）。`R` の共終数が `π` 未満の正則項 `σ` なら共終数 `σ`。
    `π` 以上なら添字の列 `γ` で対角化する（`t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`）：
    - `σ = π`：値そのもので進める（`γ_{k+1} = t[k]`）。
    - `σ` が `π` 以外の崩壊先で `Ψ_π(X) < Ψ_σ(X)`：`σ` への崩壊の塔 `γ_{k+1} = Ψ_σ(pre ⊕ (c_σ ⊕ R[γ_k]))`
      （`c_σ` は `σ` の下限のための調整）。
    - `σ = Ξ_k(e)` で `Ψ_σ(X) < Ψ_π(X)`：添字は `σ` の族の閉包。種は目標 `π` の前線の中で見える `Ψ_σ(·)` の
      最大のもの（`σ` の始点 `Ψ_σ(e+1)` 未満か、存在しなければ始点。`a2Seed`）で、添字の列は項 `Ψ_σ(β+1)` の
      基本列そのもの。添字の列の共終数（`ω` か正則項）をそのまま `t` の共終数にする（`iapp`）。
    - `σ = M_m`：`Ξ_m` の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`。始点は目標の前線の中の塔の障害の最大のもの
      （`kTop`。`0` から始めた塔が 1 段目でそれを越えるなら `0`）。近似の引数が `M_m^+` を越える場合（`kOld`）は
      仮想的な崩壊 `virtK` の塔。

`·(n+2)` と始点 `Ψ_{Ω_c}(0)` は、証明に使う「狭義の隙間」（`t` の真の部分項で `t` 未満のものは全ての `t[n]`
未満）を成り立たせるため（`·(n+1)` だと `ω[0] = 1` が `ω` の真の部分項 `1` に等しくなる）。意味論側の
`Succ.lean`・`WF/Fund.lean` の基本列 `Ψ_π(b)·(n+1)` とは添字が 1 つずれている。

### 計算量（`Memo.lean`）

`cmp`・`inC` は定義どおりに計算すると入れ子の深さについて指数的な時間がかかるので、メモ化版を作り、元の定義と
一致することを証明して `@[csimp]` で置き換えた（`cmp_eq_cmpFast`・`inC_eq_inCFast`）。呼び出される組は入力の
部分項とそこから作る項だけなので多項式個。基本列は `info` が項を下から一度だけたどって各節点の列の記述（`SeqD`）を
作り、`t[n]` は記述の木を下るだけ（対角化の添字は `n` 回の反復）で計算する。

`lake exe fstime` の実測（`ε_0`・`Ψ_{Ω_0}(Ω_1)`・`Ψ_{Ω_0}(M_1)`・`Ψ_{Ω_0}(M_1^+)`・`Ψ_{Ω_0}(M_2 + Ψ_{Ξ_1(M_1+1)}(M_1+2))`・
`Ψ_{Ω_0}(M_2 + Ψ_{Ξ_1(0)}(M_1))`）：`t[n]` の大きさは `n` に比例し、`n = 128` でも 1 ミリ秒前後。降下列
`t, t[2], t[2][2], …` をたどって項が大きくなると時間は急に伸び、大きさ 2 万で 1.5 秒前後、3 万で 2〜2.5 秒、10 万で
36 秒（`Ψ_{Ω_0}(M_1^+)` の降下列の 12 段目）、14 万で 2 分半（`Ψ_{Ω_0}(M_2 + Ψ_{Ξ_1(M_1+1)}(M_1+2))` の 12 段目）。

### 証明の構成

列の性質は、FS の公理に要る性質（`NatProps`・`BigProps`：標準形・減少・単調・共終）に、崩壊の列を部分項の列から
組み立てるための不変量を加えた `Inv`（`Inv.lean`）として、項の大きさについての帰納法で示す（`inv_all`）。

* 上界 `ub`：`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)`（`d` は切断でよい。近似 `Ψ_π(A_n)` が標準形であること
  `A_n ∈ C(A_n, Ψ_π(A_n))` を、`d = Ψ_π(A_n)` に使って示すため）。
* 隙間 `gap`：`t` の真の部分項で `t` 未満のものは `t[n]` 未満（近似の引数 `A_n` が `X` の部分項を越えるため）。
* 正則型の不変量 `BigInv` には、共終数が正則項であること（`σreg`）・共終数が項以下であること（`σle`）・
  `ξ ≤ t[ξ]`（`ge`）・添字での共終性 `lclo`（`x < t` で `x` の `σ` 未満の極大部分項が `ξ` 未満なら `x < t[ξ]`）・
  `M_m` への対角化で使う下界 `lbK`・`lbS` などを持たせる。

崩壊 `Ψ_π(X)` の列の不変量は、`X` と崩壊先の形で次のファイルに分かれ、`Inst.lean` で全ての標準形の不変量
`inv_of` にまとまる。

| 場合 | ファイル |
|---|---|
| `Ψ_{Ω_c}(0)` と `Ψ_{Ω_d}(X'+1)`（`B·(n+2)`） | `PsiMul.lean` |
| 極限 `X` の素の近似（`R` の列が `ω` 型、または共終数 `σ < π`） | `Split.lean`・`PsiLim.lean` |
| `Ψ_{Ξ_m(q)}(X'+1)`（`q < M_m`、`q < X'`）：`p` の上の `Ω` の塔 | `PsiXi.lean` |
| 対角化：添字の列による近似、目標そのものへの対角化 | `PsiDiag.lean` |
| 外に足す型の塔（`Ψ_π(X) < Ψ_σ(X)`） | `PsiOut.lean` |
| `M_m` への対角化（近似が `M_m^+` 未満：`canonK`、以上：`kOld`） | `XiIter.lean`・`KCl.lean`・`KTop.lean`・`PsiK.lean`・`Virt.lean`・`PsiKO.lean` |
| `Ξ_m(q)` への崩壊の後者（族の閉包。`q < X'`：`XiSucc`、底 `X' = q`：`XiFloor`） | `XiFam.lean`・`FamSeq.lean`・`FamApp.lean`・`FamVK.lean`・`FamBig.lean`・`XiSucc.lean`・`XiFloor.lean` |
| 外に足す型で族の閉包を添字にする場合（`Ψ_σ(X) < Ψ_π(X)`） | `PsiFam.lean` |

外に足す型で族の閉包を添字にする場合（`PsiFam.lean`）は、`σ = Ξ_k(e)`（`lev π = k`）で、`σ` の始点
`B = Ψ_σ(e+1)` は `π` の底の条件を満たさず、全ての `Ψ_π(A)` 未満（`a2_shape`）。種 `p = a2Seed σ π` は `B` 以上
`σ` 未満で、種の仮定 `SeedHyp` を満たす（`seedHyp_base`）。見える `Ψ_σ(·)` が全て列の下の点 `G` 以下の項は添字の列の
下にあり（`cf_lt_fam_nat`・`cf_lt_fam_big`）、`π` の前線は `G = p` で、`C(a, x)`（`x < t`）の元は `G = t` で
これを満たす（`cf_of_inC`・`hull_nat`・`hull_big`）。

### Bachmann 性（`Bach*.lean`・`Final.lean`）

`ω` 型の Bachmann 性 `BachHyp`（`t[n] < b < t ⇒ t[n] ≤ b[0]`）を仮定なしで示した（`bachHyp_proof`）。

* 区間の下界 `LBI x y`（区間 `(x, y]` の全ての標準形 `b` で `x ≤ b[0]`）は推移的で、`ω` 型の項の Bachmann 性は
  隣り合う項の `LBI (t[n]) (t[n+1])`（梯子）と共終性から出る（`bachHyp_of_ladder`）。
* 強い形 `BInv t`：`ω` 型なら梯子、共終数が正則項 `σ` なら添字の区間の下界の移送（`ξ ≤ η < σ`、`ξ` は `0` か
  `σ` の始点より大きい主要項で、`LBI ξ η` なら `LBI (t[ξ]) (t[η])`）。崩壊以外の項で示し、崩壊の場合に帰着する
  （`binv_all`）。崩壊の近似 `Ψ_π(pre ⊕ (c ⊕ R[ν]))` の梯子は `R` の移送と崩壊の持ち上げ（`lbi_psi_apx`）から
  出るので、対角化では添字の列の梯子を示せばよい。
* 添字の列の梯子：`Ω` について閉じた根の上の `Ω` の塔（`lbi_tower`）、`Ξ_m` の近似 `Ξ_m(pre ⊕ R[n] ⊕ P')`
  （区間に現れる `Ξ_m(E)` の始点の 0 番目が下界以上：`lbi_xi`。種 `P'` は族について閉じた点：`SeedPack`）、
  族の閉包の各枝（`seqLad_mahloVK`、種が `Ψ_{Ξ_m(q)}(β)` なら `seqLad_mahloVK_psi`）。
* 最後に残った 3 つの場合：`Ξ_m(q)` への崩壊の後者（底の種の形 `floor_seed_form` と構造的な前線の評価
  `fr_fs_low`）、`M_m` への対角化（`kOld` の仮想的な塔と `canonK` の塔）、外に足す型で族の閉包を添字にする場合
  （種 `a2Seed` は `Ψ_σ(β)` なので種つきの近似の枠組みがそのまま使える）。

| 内容 | ファイル |
|---|---|
| 梯子（`LBI`）への帰着、0 番目の基本性質 | `Bach.lean` |
| `LBI` の持ち上げ（和・`Ω`・`Ψ`）と崩壊の 0 番目の評価 | `BachLift.lean`・`BachZ.lean`・`BachPsi.lean`・`BachOm.lean`・`BachReg.lean` |
| `BInv` の枠組み（崩壊以外の項）と簡単な崩壊 | `BachMain.lean`・`BachMul.lean` |
| 素の近似・目標そのものへの対角化・外に足す型の塔 | `BachArg.lean`・`BachPlain.lean`・`BachDiagIn.lean`・`BachDiagOut.lean` |
| `Ξ` の持ち上げ、族の閉包の梯子（種つきの近似） | `BachXi.lean`・`BachFam.lean`・`BachSeed.lean`・`BachVK.lean` |
| `Ξ_m(q)` への崩壊の後者 | `BachFr.lean`・`BachFloor.lean` |
| `M_m` への対角化 | `BachDiagM.lean` |
| 外に足す型で族の閉包を添字にする場合 | `BachA2.lean` |
| Bachmann 性 `bachHyp_proof` と仮定なしの `fsNF` | `Final.lean` |

### 可算な標準形と基本列による到達（`NotNF.lean`）

Compact リポジトリの `Compact/FS/NotNF.lean`（Subsp の `FundSys.NOT`）と同じステートメント。この系の最初の非可算
基数は `Ω_0` なので、可算な標準形は `Ω_0` 未満の標準形。基本列は `fsNF` のもの（`fundNF props_all`、`fsNF_fund`）。
Bachmann 性は使わない。

* 始点 `notBase n = Ψ_{Ω_0}(M_{n+1})` は可算で共終数 `ω` の極限（`dom_notBase`）。可算な `t` は、`n` を部分項の
  階の最大値に取ると始点未満（`lt_notBase`：節点の引数が全て `M_{n+1}` 未満なので `t ∈ C(M_{n+1}, Ψ_{Ω_0}(M_{n+1}))`）。
* 正則項は全て `Ω_0` 以上なので、可算な項の共終数は `0`・`1`・`ω` のいずれか（`dom_countable`）。
* 順序数項 `IsOT`：始点 `notBase n` から基本列 `t ↦ t[n]`（`n` は自然数）の反復で得られる標準形。
  `isOT_iff : IsOT t ↔ t < Ω_0`、`NOT_eq : NOT = {t : NF // t < Ω_0}`（下への閉包は基本列の共終性と整列性から）。
* `NOTFundLt_iff_lt`：基本列の一歩（`NOTStep`）の推移閉包は項の順序と一致する。
* `countable_iff_reach : t < Ω_0 ↔ ∃ n, TransGen FundStep t (Ψ_{Ω_0}(M_{n+1}))` と、その集合の形
  `countable_eq_reach`：可算な標準形の集合は、可算な極限の始点から基本列の一歩の推移閉包で到達できる元の集合。

### 定義を直した点

基本列の定義は、証明の途中で見つかった次の誤りを直したもの。

* `M_1` への対角化の塔を `0` から始めると、`Ψ_{Ξ_1(Ξ_1(M_1))}(M_1)` で閉じた点 `Ξ_1(M_1)` を越えられず共終性が
  破れた。塔の始点を目標の前線の中の障害にした（`kTop`）。
* `Ψ_{Ξ_m(d)}(X'+1)` の列を常に `p = Ψ_{Ξ_m(d)}(X')` の上の `Ω` の塔にしていたのは、`d ≥ M_m` で誤り
  （`Ψ_{Ξ_1(M_1)}(M_1+2)` 未満に `Ξ_1(Ψ_{Ξ_1(M_1)}(M_1+1))` があり、塔はそれを越えない）。目標の族の閉包に直した。
* 外に足す型の対角化で `Ψ_σ(X) < Ψ_π(X)` のとき、添字の族の閉包の共終数が正則項になる場合がある
  （`E = Ψ_{Ω_{M_1+1}}(Ω_1)`、`σ = Ξ_1(E)`、`X = E + σ`、`π = Ξ_1(Ψ_σ(X)+1)` では `Ω_1`）。添字の列を常に `ω` 型と
  して扱っていたので `t[n]` が全て等しくなっていた。添字の列の共終数をそのまま `t` の共終数にした（`iapp`）。
* Bachmann 性の反例 1：上の場合の添字を、目標の前線の最大元 `c`（`Ω` について閉じていない）の上の `Ω` の塔に
  していた。`σ = Ξ_1(0)`、`P = Ψ_σ(M_1)`、`S1 = Ψ_{Ξ_1(σ+1)}(σ + P + 2)`、`c = Ψ_{Ω_{P+1}}(5)`、`π = Ω_{c+1}`、
  `t = Ψ_π(S1 + σ)` で、`d = Ψ_{Ω_{P+1}}(ω)` の `b = Ψ_π(S1 + Ω_d)` は `t[0] < b < t` だが `b[0] < t[0]`。
* Bachmann 性の反例 2：種を `Ω` について閉じた根の塔の元に上げても足りない。`e = Ψ_{Ω_{M_1+1}}(ω)`、
  `σ = Ξ_1(e)`、`X = Ψ_{Ω_{M_1+1}}(σ)`、`S = Ψ_σ(X)`、`π = Ω_{f+1}`（`f = Ψ_{Ω_{S+1}}(0)`）の `t = Ψ_π(X)` では、
  種 `Ω_{S+1}` の上の近似 `y_n = Ξ_1(H + Ω_{S+1})`（`H = e[n]`）の区間に `b = Ψ_{Ξ_1(E)}(E+1)`（`E = H + M_1 + S`、
  `b[0] = Ξ_1(H + S) < y_n`）が入る。種を目標の前線の中で見える `Ψ_σ(·)` の最大のもの（`a2Seed`）にした。
* ほかに Bachmann 性の証明のため、外に足す型の塔の調整（`c_σ`）と近似の調整（`0` か `rt + 1`）を整理した。

### 検査と計時

基本列の性質は全て Lean で証明してあるので、以下は開発中に使った補助の検査。

* `FSTest.lean`（`lake exe fstest`）：標準形の標本の各項について、列の項が標準形・元の項未満・単調・共終、`ω` 型の
  Bachmann 性を標本の中で確かめる。引数が数 `S` なら大きさ `S` 以下の標準形全て（大きさ 7 以下で 2397 個）、
  `seeds S D`・`wrap S D` は手で選んだ種の項・それに `Ω`・`Ξ`・`Ψ` をかぶせた項の標本、`probe`・`probeInv`・
  `probeBach` などは大きな崩壊先・引数を組み合わせた標本での個別の性質の検査、`time` は計時。ファイルが大きいので、
  ビルドに多くのメモリ（約 20GB）を使う。
* `FSTime.lean`（`lake exe fstime`）：上の「計算量」の計時。
* `FSProbe.lean`（`lake exe fsprobe`）：外に足す型で族の閉包を添字にする場合（`PsiFam.lean`）の項 1707 個について、
  列の性質・添字の列と `t` の Bachmann 性を確かめる。

## ファイル

意味論と記法系：

* `Mahlo/Ordinal.lean`：順序数（Compact から変更なしでコピー）
* `Mahlo/Setting.lean`：基数の設定（弱 Mahlo 基数の列）と崩壊関数 `Ξ`・`Ψ` の定義
* `Mahlo/Basic.lean`：`C(α, β)` の大きさ、閉非有界集合、`Ξ`・`Ψ` が値をとること
* `Mahlo/Compare.lean`：崩壊関数の値どうしの比較（Lemma 4.14、分離補題）
* `Mahlo/Notation.lean`：記法系（項、`cmp`、`inC`、`baseOf`、`isNF`）
* `Mahlo/Gen.lean`：`C(γ, δ)` の元の分解と、生成子の値の一意性
* `Mahlo/Good.lean`：項の値 `val` と、標準形の意味論版 `Good`
* `Mahlo/Correct.lean`：`cmp`・`inC`・`baseOf` の正しさ
* `Mahlo/NF.lean`：`isNF` と `Good` の一致、比較の正しさと一意性
* `Mahlo/Succ.lean`：後続基数への崩壊の基本列（意味論）
* `Mahlo/Complete.lean`：標準形の値の集合と `C(Λ, 0)` の一致、弱 Mahlo 基数の列からの整列性
* `Mahlo/WF/Syntax.lean`・`Mahlo/WF/Order.lean`・`Mahlo/WF/Wmax.lean`：構文的な順序の性質と整列性
* `Mahlo/WF/Fund.lean`：後続基数への崩壊の基本列の構文的な証明
* `Mahlo/Unconditional.lean`：仮定なしの結論と順序型による値 `ordVal`
* `Mahlo/Agree.lean`：二つの意味論の一致
* `Mahlo/Design.lean`：設計の比較規則の仮定なしの形、到達不能基数への崩壊の基本列、古典論理が要る理由

基本列（`Mahlo/FS`）：

* `Class.lean`：基本列の公理（`Well_Order`・`Cof`・`FS`）
* `Memo.lean`：`cmp`・`inC` のメモ化版（多項式時間）と一致の証明
* `Def.lean`・`Seq.lean`：基本列の定義（`dom`・`fund`、列の記述 `SeqD`）
* `Arith.lean`・`CLem.lean`：和・自然な和・倍の性質と、`C(g, d)` への所属
* `Dom.lean`：解析 `info` の基本性質、共終数の分類、0・後者・自然数の公理
* `Order.lean`：`NF` の整列順序
* `Props.lean`：FS の公理に要る列の性質（`NatProps`・`BigProps`）と、構造的な場合
* `Below.lean`：崩壊の候補 `Ψ_π(A)` との比較（移し替え・切断）
* `Base.lean`：`Ξ_n(d)` の列の始点の標準形
* `Clo.lean`：共終性の道具（閉じた点、移し替えの一歩、成分による帰納法）
* `Inv.lean`：列の不変量（上界・隙間など）と構造的な場合、崩壊の場合への帰着
* `PsiMul.lean`・`Split.lean`・`PsiLim.lean`・`PsiXi.lean`・`PsiDiag.lean`・`PsiOut.lean`・`PsiAll.lean`：崩壊の列の
  各場合（`B·(n+2)`・素の近似・`Ω` の塔・対角化・外に足す型の塔）と対角化の場合分け
* `XiIter.lean`・`KCl.lean`・`KTop.lean`・`PsiK.lean`・`Virt.lean`・`PsiKO.lean`：`M_m` への対角化（`Ξ_m` の反復の塔、
  閉じた点の探索、塔の始点 `kTop`、仮想的な崩壊 `virtK`）
* `XiFam.lean`・`FamSeq.lean`・`FamApp.lean`・`FamVK.lean`・`FamBig.lean`：族の閉包 `mahloVK` の列の仕様
* `XiSucc.lean`・`XiFloor.lean`：`Ξ_m(q)` への崩壊の後者（族の閉包）
* `PsiFam.lean`：外に足す型で族の閉包を添字にする場合（種 `a2Seed`）
* `Inst.lean`：全ての標準形の列の不変量 `inv_of` と、Bachmann 性を仮定した `FS NF`（`fsNFOf`）
* `Bach.lean`・`BachLift.lean`・`BachZ.lean`・`BachPsi.lean`・`BachOm.lean`・`BachReg.lean`・`BachMain.lean`・
  `BachMul.lean`・`BachArg.lean`・`BachPlain.lean`・`BachDiagIn.lean`・`BachDiagOut.lean`・`BachXi.lean`・
  `BachFam.lean`・`BachSeed.lean`・`BachVK.lean`・`BachFr.lean`・`BachFloor.lean`・`BachDiagM.lean`・`BachA2.lean`：
  Bachmann 性（強い形 `BInv`）の証明
* `Final.lean`：Bachmann 性 `bachHyp_proof` と仮定なしの `fsNF`
* `NotNF.lean`：可算な標準形全体と、可算な極限の始点から基本列で到達できる元全体の一致

実行ファイル：

* `Main.lean`（`lake exe mahlo`）：項の例と `isNF`
* `FSTest.lean`（`lake exe fstest`）・`FSTime.lean`（`lake exe fstime`）・`FSProbe.lean`（`lake exe fsprobe`）：
  基本列の検査と計時
