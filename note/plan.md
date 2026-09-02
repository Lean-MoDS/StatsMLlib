# Rademacher 複雑度評価と汎化評価を接続するための実装計画（StatsMLlib 版）

## 0. この文書について

### 0.0 この作業の目的

この作業には目的が 2 つある。

1. **上流の設計に沿って StatsMLlib を refactor する。** 上流 `auto-res/lean-rademacher` の
   コード変更をそのまま取り込むのではなく、その実装計画が示す設計（経験複雑度 → 期待複雑度 →
   一様偏差 → 余剰誤差、という bridge の連鎖）に沿って StatsMLlib 側を組み立て直す。
   したがってモジュールの置き場、宣言の形、正準とする定義は StatsMLlib の
   `ARCHITECTURE.md` に従い、上流と異なってよい。実際、`coveringNumber`（付録 B-1）、
   `LipschitzParameter` の置き場（§0.5）、`Main.lean` と `ForMathlib` 層を作らないこと
   （§0.2）は上流と異なる判断になっている。
2. **FoML 由来の API と StatsMLlib 独自の統計的学習理論 API の重複を解消する。**
   対処は付録 B にある。重複はこの作業の副次的な制約ではなく、解消そのものが成果物である。
   具体的には B-3（entropy integral 3 系統）、B-5（稠密可算化 bridge 2 系統）、
   B-6（ERM 述語 2 つ）、B-8（maximal inequality 3 系統）を扱う。

作業は一人で行い、PR は細かく分ける。ライブラリの設計方針に触れる PR は
その都度議論する（どの PR がそれに当たるかは付録 C に明示した）。

### 0.1 出典

本文書は `auto-res/lean-rademacher` の `note/plan.md`（ブランチ `ss`, HEAD `d50ea5c`）を、
StatsMLlib のモジュール構成に合わせて書き直したものである。原文は
[`note/upstream/plan.md`](upstream/plan.md) にそのまま置いてある。あわせて
[`note/upstream/summary.md`](upstream/summary.md) が上流実装の全体像を記述している。

上流での実装対象は commit `3819e1e` 以降の 15 commit（`ce9a506` 〜 `bc33376`）であり、
StatsMLlib の現行コードはその直前（`3819e1e`）に相当する。したがって本計画の項目は
**すべて StatsMLlib では未着手**である。

### 0.2 読み替えの原則

1. **ファイルパス**は §0.3 の対応表に従って StatsMLlib のモジュールへ読み替える。
   §2 以降の本文中のパスはすべて置換済みで、`FoML/...` は §0.3 の対応表にしか残っていない。
2. **宣言名**は読み替えない。StatsMLlib は上流からの取り込み時にモジュール名だけを
   変更し、宣言はほぼ root namespace のまま同名で保持している。したがって
   `empiricalRademacherComplexity`、`uniformDeviation`、`coveringNumber`、
   `linear_predictor_l2_bound'` などは上流と同じ名前で参照できる。
   唯一の例外は `EmpiricalProcess.empiricalNorm`（`Fin n → ℝ` を取る正準版）で、
   上流と同じ「標本添字版」`empiricalNorm S f` は
   `LearningTheory/EmpiricalProcess/FunctionClass.lean` に `abbrev` として用意されているため、
   上流のコードはそのまま通る。
3. **「既存の」「現在の」「すでに」の時点**に注意する。§12 以降（上流 Phase 6 以降）は
   上流が Phase 5 まで終えた時点で書かれているため、この計画自身の Phase 1〜5 で
   追加する宣言を「既存」と呼んでいる箇所がある。StatsMLlib の現状に存在するのは
   §0.3 の対応表で「既存モジュールへ追記するもの」に挙げた 24 モジュールの中身だけである。
   紛らわしい箇所には「（§5.1 で追加する）」のように補記した。
4. **チェックボックス**は StatsMLlib での進捗を表す。原文で `[x]` だった項目も、
   ここでは移植前なのですべて `[ ]` にしてある。原文で `[ ]` だった項目
   （§18.2 の risk minimizer 存在）は上流でも未実施であることを併記した。
5. **`Main.lean` / `FoML.lean` に相当するものは StatsMLlib に置かない。**
   `ARCHITECTURE.md`「Module naming」が `Main.lean` の追加を禁じており、全体 umbrella も
   宣言を持たないことになっている。上流 `FoML/Main.lean` は 562 行あるが定理は 0 本で、
   13 個の `example` と docstring だけなので、各 `example` は対応するモジュール末尾の
   受け入れテストとして分散配置する。本文で原文が `Main.lean` を指していた箇所は
   「公開 example」と書き、配置先を各所に明記した。
6. **`ForMathlib` 層は作らない。** `ARCHITECTURE.md`「Refactoring decisions」により
   `ForMathlib` は layer-one ディレクトリではなくなっている。上流の
   `FoML/ForMathlib/X/Y.lean` は主題ディレクトリへ直接置く。

StatsMLlib 固有の制約（import 方向、命名規約）は `ARCHITECTURE.md` に従う。すなわち

```text
{Order, MeasureTheory, Topology, LinearAlgebra}  →  Analysis  →  Probability
    →  LearningTheory  →  Statistics
```

の向きにのみ import してよい。

### 0.3 モジュール対応表

#### 既存モジュールへ追記するもの

| 上流モジュール | StatsMLlib モジュール |
|---|---|
| `FoML/Defs.lean` | `StatsMLlib/LearningTheory/Rademacher/Defs.lean`, `StatsMLlib/LearningTheory/UniformDeviation/Defs.lean` |
| `FoML/Probability/Expectation.lean` | `StatsMLlib/Probability/Moments/Expectation.lean` |
| `FoML/Probability/MeasurePi.lean` | `StatsMLlib/Probability/Independence/FinsetPi.lean` |
| `FoML/Probability/Hoeffding.lean` | `StatsMLlib/Probability/Concentration/Hoeffding.lean` |
| `FoML/Probability/McDiarmid.lean` | `StatsMLlib/Probability/Concentration/McDiarmid.lean` |
| `FoML/Rademacher/Signs.lean` | `StatsMLlib/LearningTheory/Rademacher/Signs.lean` |
| `FoML/Rademacher/Symmetrization.lean` | `StatsMLlib/LearningTheory/Rademacher/Symmetrization.lean` |
| `FoML/Rademacher/Expectation.lean` | `StatsMLlib/LearningTheory/Rademacher/Complexity.lean` |
| `FoML/Rademacher/BoundedDifference.lean` | `StatsMLlib/LearningTheory/UniformDeviation/BoundedDifference.lean` |
| `FoML/Entropy/CoveringNumber.lean` | `StatsMLlib/Topology/MetricSpace/CoveringNumber/Basic.lean` |
| `FoML/Entropy/PseudoMetric.lean` | `StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean`, `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean` |
| `FoML/Entropy/MaximalInequality.lean` | `StatsMLlib/Probability/Concentration/Maximal.lean` |
| `FoML/Entropy/Massart.lean` | `StatsMLlib/LearningTheory/Rademacher/Massart.lean` |
| `FoML/Entropy/Dudley.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` |
| `FoML/Generalization/Dudley.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` |
| `FoML/Generalization/Countable.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` |
| `FoML/Generalization/Separable.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` |
| `FoML/Model/LinearPredictorL2.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
| `FoML/Generalization/LinearPredictorL2.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
| `FoML/Model/LinearPredictorL1.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
| `FoML/Generalization/LinearPredictorL1.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
| `FoML/ForMathlib/Probability/Moments.lean` | `StatsMLlib/Probability/Moments/Cumulant.lean` |
| `FoML/ForMathlib/Topology/SeparableSpace.lean` | `StatsMLlib/Topology/SeparableSpace/Supremum.lean` |
| `FoML/ForMathlib/Analysis/SumIntegralComparisons.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean`（取り込み済み） |

上流 `Model/*` と `Generalization/*` が同一主題で分かれている箇所は、StatsMLlib では
既に 1 ファイルに統合されている（`LinearPredictor/L1.lean`, `L2.lean`）。同じ理由で
`Entropy/Dudley` と `Generalization/Dudley` は `Rademacher/Dudley.lean` に同居する。
新規主題も同じ方針を採り、固定標本評価と汎化評価を 1 ファイルに置く。

#### 新規に作るもの

| 上流モジュール | StatsMLlib モジュール | 備考 |
|---|---|---|
| `FoML/Rademacher/Reindex.lean` | `StatsMLlib/LearningTheory/Rademacher/Reindex.lean` | |
| `FoML/Entropy/FiniteClass.lean` + `FoML/Generalization/FiniteClass.lean` | `StatsMLlib/LearningTheory/Rademacher/FiniteClass.lean` | |
| `FoML/Entropy/LipschitzParameter.lean` + `FoML/Generalization/LipschitzParameter.lean` | `StatsMLlib/LearningTheory/Rademacher/LipschitzParameter.lean` | |
| `FoML/Learning/Contraction.lean` | `StatsMLlib/LearningTheory/Rademacher/Contraction.lean` | |
| `FoML/Model/HilbertPredictor.lean` | `StatsMLlib/LearningTheory/FunctionClass/HilbertPredictor.lean` | |
| `FoML/Model/RKHS.lean` + `FoML/Generalization/RKHS.lean` | `StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean` | |
| `FoML/Generalization/Confidence.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean` | |
| `FoML/Learning/Defs.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Defs.lean` | 新規ディレクトリ |
| `FoML/Learning/ERM.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Basic.lean` | |
| `FoML/Generalization/Learning.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Generalization.lean` | |
| `FoML/Generalization/RKHSLearning.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/KernelPredictor.lean` | |
| `FoML/ForMathlib/MeasureTheory/Measure/Real.lean` | `StatsMLlib/MeasureTheory/Measure/Real.lean` | 新規ディレクトリ |
| `FoML/ForMathlib/Probability/Confidence.lean` | `StatsMLlib/Probability/Concentration/Confidence.lean` | |
| `FoML/ForMathlib/Analysis/FiniteSample.lean` | `StatsMLlib/Analysis/FiniteSample.lean` | 深さ 2（§0.4） |
| `FoML/ForMathlib/Order/ISup.lean` | `StatsMLlib/Order/IndexedSupremum.lean` | 新 layer-one `Order`（§0.4） |

`LearningTheory/EmpiricalRiskMinimization/` は StatsMLlib に存在しない second-level ディレクトリなので、
`ARCHITECTURE.md` の構成図の更新が必要になる。`EmpiricalRiskMinimization/Defs.lean` は
「`Defs.lean` はディレクトリが主題を特定する場合のみ可」の条件を満たす。

#### 対応するものを作らない上流ファイル

| 上流 | 扱い |
|---|---|
| `FoML.lean` | 作らない。umbrella は `ARCHITECTURE.md` により宣言を持てない。 |
| `FoML/Main.lean` | 作らない。`example` を各モジュール末尾へ分散（§0.2-5）。 |

### 0.4 確定した命名

着手前に決めるべきだった 3 点は次のとおり確定した。いずれも `ARCHITECTURE.md`
「Module naming」と既存ディレクトリの表記に合わせている。

1. **`StatsMLlib/Order/IndexedSupremum.lean`**（新 layer-one `Order`）

   内容は `ciSup_comp_of_surjective` と `abs_ciSup_sub_ciSup_le` の 2 本で、
   条件付き完備束および ℝ の順序的事実である。Mathlib の `Mathlib/Order/` と同じ位置づけで、
   `{MeasureTheory, Topology, LinearAlgebra}` と同じ最下層に置く。
   ファイル名を `ISup` ではなく `IndexedSupremum` にしたのは、上流 `SeparableSpaceSup.lean` を
   `Topology/SeparableSpace/Supremum.lean` として取り込んだ既存の表記に合わせるため。

   `ARCHITECTURE.md` の layer 表・構成図・import 方向図に `Order` を追記する
   （tier は `{Order, MeasureTheory, Topology, LinearAlgebra}` の最下層）。

2. **`StatsMLlib/Analysis/FiniteSample.lean`**（深さ 2）

   内容は `Fin n` 上の正規化和に関する初等評価 2 本。
   `StatsMLlib/Probability/SmallBall.lean` が深さ 2 の先例なので、
   1 ファイルのために subject ディレクトリを新設しない。

3. **`StatsMLlib/LearningTheory/EmpiricalRiskMinimization/`**

   `ARCHITECTURE.md` は「provenance や project の略語ではなく完全な主題名」を求めており、
   既存の layer-two はすべて `EmpiricalProcess`, `FunctionClass`, `UniformDeviation`,
   `LeastSquares` のように綴られている。したがって `ERM/` ではなく綴った形を採る。
   中身は risk / empirical risk / ERM 述語 / oracle inequality なので主題は特定できる。

   同じ理由で、上流 `Model/RKHS.lean` + `Generalization/RKHS.lean` の移植先は
   `FunctionClass/RKHS.lean` ではなく
   **`StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean`** とする。
   既存の `FunctionClass/LinearPredictor/` および新規の
   `FunctionClass/HilbertPredictor.lean` と並ぶ名前になり、
   内容（特徴写像から誘導される kernel と、その予測器クラスの評価）とも一致する。
   上流 `Generalization/RKHSLearning.lean` は
   `EmpiricalRiskMinimization/KernelPredictor.lean` とする。

`ARCHITECTURE.md` と `FILE_TREE.md` への反映は、該当ファイルを作る最初の PR に含める。

### 0.5 移植対象から外す項目

- **上流 Phase 9（モジュール階層の整理）**: StatsMLlib は 2026-07 の refactor で独自の
  subject-first 階層へ移行済み。対応する作業はない。§0.3 の対応表がその成果に相当する。
- **`FoML/WIP/RademacherProperty.lean` の削除と `.gitattributes` の改行正規化**: 上流固有。
  StatsMLlib には該当ファイルがない。
- **`data/Mohri_FML.pdf`**（§16.1 の参照文献 PDF）: リポジトリに取り込まない。書誌情報は
  docstring に書く。
- **Mathlib の `Metric.coveringNumber` への移行**（§13.7）: 値域が `ℕ` と `ℕ∞` で異なり、
  開球・閉球の差もあるため今回はやらない。

## 2. 現状の型に由来する論点

### 2.1 経験量から期待量への移行

定義から

```lean
rademacherComplexity n f μ X =
  μⁿ[fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]
```

である。したがって

```lean
∀ S, empiricalRademacherComplexity n f S ≤ C
```

と被積分関数の可積分性があれば、確率測度上の積分の単調性により

```lean
rademacherComplexity n f μ X ≤ C
```

を得られる。Lean の Bochner 積分は非可積分な関数に対しても値を持つため、非可積分時に積分が `0` となる仕様を利用して証明を短絡させず、共通補題では可積分性を明示する。

### 2.2 汎化評価の事象の包含

既存の高確率定理が評価する悪い事象は

```text
2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation ...
```

である。`rademacherComplexity n f μ X ≤ C` なら

```text
{2 * C + ε ≤ uniformDeviation}
  ⊆
{2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation}
```

なので、`measure_mono` によって既存の tail 評価をそのまま再利用できる。

### 2.3 線形予測器の定義域

既存の汎化定理は `∀ i x, |f i x| ≤ b` を関数の全定義域で仮定する。したがって、入力を周辺の Euclidean space 全体とした非自明な線形関数には直接適用できない。

end-to-end の定理では次の有界な部分型を入力空間および添字空間として使う。

- $\ell_2$ 版:
  - 入力: `Metric.closedBall 0 X`
  - 重み: `Metric.closedBall 0 W`
- $\ell_1/\ell_\infty$ 版:
  - 入力: `LinftyBall Xinf`
  - 重み: `L1Ball W`

既存の経験複雑度評価は部分型の値を周辺空間へ写して適用し、関数合成に関する経験 Rademacher 複雑度の等式で部分型版へ戻す。

### 2.4 Dudley の片側版

現在証明済みなのは

```lean
empiricalRademacherComplexity_without_abs n F S
  ≤ empiricalRademacherComplexity n F S
```

であり、この向きから Dudley の上界を絶対値付き版へ移すことはできない。

関数クラスを

```text
F± = {F i | i ∈ ι} ∪ {-F i | i ∈ ι}
```

と符号対称化すれば、各符号列について

```text
sup_i |A i| = sup_(i,s) s * A i
```

となる。この等式を Lean 上で明示的に証明してから、`F±` に既存の Dudley 定理を適用する。

## 3. 追加する共通補題

### 3.1 経験 Rademacher 複雑度の基本補題

`StatsMLlib/LearningTheory/Rademacher/Signs.lean` に以下を追加する。

1. 非負性

   ```lean
   empiricalRademacherComplexity_nonneg
   ```

   有限平均の係数、有限和の各項、絶対値の上限がすべて非負であることから示す。

2. 定義域の写像との可換性

   ```lean
   empiricalRademacherComplexity_comp
   ```

   想定する主張は次の形である。

   ```lean
   empiricalRademacherComplexity n
       (fun i x ↦ g i (q x)) S
     =
   empiricalRademacherComplexity n g (q ∘ S)
   ```

   線形予測器の部分型版を既存定理へ接続する際に使う。同様の補題が Dudley の符号対称化でも必要になれば、片側版についても追加する。

3. 可測性・可積分性

   可算添字、各 `f i ∘ X` の可測性、一様有界性の下で

   ```lean
   Measurable fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)

   Integrable (fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)) μⁿ
   ```

   を示す補題を追加する。既存の
   `measurable_signed_sup_sum_fst_core`,
   `abs_sum_sup_signed_le_pow_mul_bound` で使われている議論を正規化済みの定義へまとめ直す。

### 3.2 経験量から期待量への共通 bridge

`StatsMLlib/LearningTheory/Rademacher/Complexity.lean` に次の二段階の補題を追加する。

1. a.e. の上界を積分する一般形

   ```lean
   rademacherComplexity_le_of_ae_empirical_le
   ```

   主な仮定:

   - `[IsProbabilityMeasure μ]`
   - `Integrable (fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ`
   - `∀ᵐ ω ∂μⁿ, empiricalRademacherComplexity n f (X ∘ ω) ≤ C`

   結論:

   ```lean
   rademacherComplexity n f μ X ≤ C
   ```

2. 全固定標本に対する上界を受け取る簡便形

   ```lean
   rademacherComplexity_le_of_empirical_le
   ```

   主な仮定:

   - 上記の可積分性
   - `∀ S, empiricalRademacherComplexity n f S ≤ C`

   一般形に `Filter.Eventually.of_forall` を渡す薄い wrapper とする。

可算クラス用には、3.1 の可積分性補題から可積分性を自動で補う系も用意する。可分クラス用には `RademacherComplexity_eq` による稠密可算部分クラスへの還元を優先し、可積分性の重複証明を避ける。

## 4. 汎化評価側の共通 corollary

`StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` に、既知の定数 `C` を閾値へ代入する公開定理を追加する。

候補名:

```lean
uniform_deviation_expectation_le_of_empirical_le_countable
uniform_deviation_expectation_le_of_empirical_le_separable
uniform_deviation_tail_bound_countable_of_empirical_le
uniform_deviation_tail_bound_separable_of_empirical_le
```

期待値版では既存の
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`
と `rademacherComplexity n f μ X ≤ C` を合成し、

```text
E[uniformDeviation] ≤ 2 * C
```

を示す。可分クラス版は既存の稠密可算化の等式を経由して導く。

まず定数を最適化済みの既存定理

```lean
uniform_deviation_tail_bound_countable_of_pos
uniform_deviation_tail_bound_separable_of_pos
```

に対応する版を実装する。必要性が確認できた場合のみ、自由な `t` を取る版も薄い wrapper として追加する。

主張の形は次のようにする。

```text
仮定:
  ∀ S, empiricalRademacherComplexity n F S ≤ C

結論:
  P(2 * C + ε ≤ uniformDeviation)
    ≤ exp(-n * ε^2 / (2 * b^2))
```

証明は次の二段階に限定する。

1. 3.2 により `rademacherComplexity n f μ X ≤ C` を示す。
2. 2.2 の事象包含と既存の tail 定理を使う。

この共通 corollary を個別モデルの定理から再利用し、モデルごとに積分・事象包含を再証明しない。

## 5. 線形予測器の end-to-end corollary

### 5.1 $\ell_2$ 線形予測器

`StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` に、入力と重みの両方を有界球の部分型として受け取る関数と経験評価 wrapper を追加する。

候補名:

```lean
linearPredictorL2
linear_predictor_l2_empirical_bound
```

設定:

```text
ι  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W
𝒳  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X
f w x = ⟪(w : EuclideanSpace ...), (x : EuclideanSpace ...)⟫
```

証明する評価:

```text
empiricalRademacherComplexity n f S
  ≤ X * W / sqrt n
```

既存の `linear_predictor_l2_bound'` と
`empiricalRademacherComplexity_comp` から導く。

続いて同じファイルの公開 API として以下を追加する。

```lean
linear_predictor_l2_rademacher_complexity_bound
linear_predictor_l2_uniform_deviation_expectation_bound
linear_predictor_l2_uniform_deviation_tail_bound
```

前者:

```text
rademacherComplexity n f μ Z
  ≤ X * W / sqrt n
```

後者:

```text
P(2 * (X * W / sqrt n) + ε ≤ uniformDeviation)
  ≤ exp(-n * ε^2 / (2 * (X * W)^2))
```

主な仮定:

- `0 < n`, `0 < X`, `0 < W`
- `Z : Ω → Metric.closedBall 0 X`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

汎化定理に必要な一様有界性は Cauchy--Schwarz により

```text
|f w x| ≤ W * X
```

と示す。重み球が可分かつ第一可算であること、パラメータに関する連続性、入力に関する可測性を確認し、自然な非可算クラスなので可分クラス版の汎化定理を使う。

### 5.2 $\ell_1/\ell_\infty$ 線形予測器

`StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` に次を追加する。

```lean
linearPredictorL1
linear_predictor_l1_empirical_bound
```

設定:

```text
ι  = L1Ball W
𝒳  = LinftyBall Xinf
f w x = ∑ j, (w : EuclideanSpace ...) j * (x : EuclideanSpace ...) j
```

経験評価:

```text
empiricalRademacherComplexity n f S
  ≤ (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
```

既存の `linear_predictor_l1_bound'` と定義域写像の補題から導く。

同じファイルに以下を公開する。

```lean
linear_predictor_l1_rademacher_complexity_bound
linear_predictor_l1_uniform_deviation_expectation_bound
linear_predictor_l1_uniform_deviation_tail_bound
```

高確率評価の閾値には上の経験複雑度上界を、指数部の一様有界定数には

```text
b = Xinf * W
```

を使う。`abs_sum_mul_le_l1_mul` と部分型の条件から
`|f w x| ≤ Xinf * W` を示す。

主な仮定:

- `0 < d`, `0 < n`, `0 < Xinf`, `0 < W`
- `Z : Ω → LinftyBall Xinf`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

## 6. Dudley の絶対値付き版

### 6.1 符号対称化の定義と等式

`StatsMLlib/LearningTheory/Rademacher/Signs.lean` に、例えば

```lean
def signSymmetrization (F : ι → 𝒳 → ℝ) :
    ι × Bool → 𝒳 → ℝ
```

を追加し、`Bool` の一方を `F i`、他方を `-F i` とする。

固定標本上で関数値が一様有界という仮定の下で、条件付き上限が有限であることを明示して次を証明する。

```lean
empiricalRademacherComplexity_eq_without_abs_signSymmetrization
```

主張:

```lean
empiricalRademacherComplexity n F S
  =
empiricalRademacherComplexity_without_abs n
  (signSymmetrization F) S
```

`iSup` の書き換えでは上限有界性を省略しない。既存の
`empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity`
を逆向きに使用しないことを証明レビューの確認項目とする。

併せて、もともと負号で閉じたクラス向けに

```lean
empiricalRademacherComplexity_eq_without_abs_of_neg_closed
```

を用意する。この場合はクラスを拡大せず、元の covering number をそのまま Dudley の右辺に使える。

### 6.2 empirical norm と total boundedness の移送

次の 3 つを追加する。置き場は所有者に合わせて分ける。

1. `empiricalNorm S (-f) = empiricalNorm S f`
   → `StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean`（正準版で証明）と
   `.../FunctionClass.lean`（標本添字版への移送）。
2. 正側・負側の
   `EmpiricalFunctionSpace F S` から
   `EmpiricalFunctionSpace (signSymmetrization F) S` への写像が isometry であること
   → `EmpiricalFunctionSpace` の所有者である
   `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean`。
3. 元の関数空間全体が totally bounded なら符号対称化後も totally bounded であること
   → `signSymmetrization` に依存するので
   `StatsMLlib/LearningTheory/Rademacher/Dudley.lean`。

候補名:

```lean
signSymmetrization_totallyBounded
```

正側と負側の像がそれぞれ totally bounded であり、その有限和集合が符号対称化後の全体になることから示す。この補題を名前付きで定義し、`coveringNumber` の引数となる total boundedness の証明項を安定させる。

なお `empiricalNorm S f` は
`StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean` の `abbrev` であり、
その実体は `StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean` の
`EmpiricalProcess.empiricalNorm n (fun i ↦ f (S i))` である。負号不変性は
正準版の側で証明し、標本添字版へは `abbrev` の展開で移す。

### 6.3 絶対値付き Dudley 定理

`StatsMLlib/LearningTheory/Rademacher/Dudley.lean` に内部定理と公開 wrapper を追加する。

候補名:

```lean
dudley_entropy_integral_abs
dudley_entropy_integral_bound_abs
```

基本形の結論:

```text
empiricalRademacherComplexity n F S
  ≤ 4 * ε
    + 12 / sqrt n
      * ∫ u in ε..c/2,
          sqrt (log (coveringNumber of signSymmetrization(F) at u))
```

証明順:

1. 6.1 の等式で絶対値付き経験量を符号対称化クラスの片側経験量へ変換する。
2. `empiricalNorm` の上界を `F` から `signSymmetrization F` へ移す。
3. 6.2 で total boundedness を移す。
4. 既存の `dudley_entropy_integral'` を適用する。

負号で閉じたクラスについては、符号対称化した covering number ではなく元の covering number を使う専用 corollary を追加する。

余力があれば、正負二つの cover を合併して

```text
N(signSymmetrization F, u) ≤ 2 * N(F, u)
```

も証明する。ただし、絶対値付き Dudley 定理の成立には必須とせず、core の接続を先に完了する。

## 7. Dudley から期待量・汎化評価への接続

Dudley の右辺は標本 `S` に依存するため、固定標本版だけから標本非依存の数値上界は得られない。公開 corollary では、この点を仮定として明示する。

以下を満たす標本非依存の `C` を受け取る。

```text
すべての S について
  4 * ε
    + 12 / sqrt n * entropyIntegral(signSymmetrization F, S)
  ≤ C
```

また、すべての `S` について Dudley の norm 条件と total boundedness 条件を仮定する。6.3 により

```lean
∀ S, empiricalRademacherComplexity n F S ≤ C
```

を作り、3.2 と 4 の共通定理へ渡す。

候補名:

```lean
rademacher_complexity_le_dudley_of_uniform_entropy
uniform_deviation_tail_bound_separable_of_uniform_dudley
```

Phase 4 までの決定論的閾値版に続き、Phase 5 では経験 Rademacher 複雑度の bounded-difference 評価と下側集中を追加し、Dudley の右辺を観測標本に依存する閾値として残す。

## 8. 上流 Phase と本文の対応

上流の phase は時系列であり、依存関係で切ったものではない。**実装の順序は付録 C-3 が唯一の正**。
この表は上流の記述と読み合わせるためだけに置く。

§3–§7 と §12 は「何を、どの形で述べるか」を書いた節で、チェックボックスを持たない。
進捗の追跡は付録 C-3 の PR 単位で行う。

| 上流 Phase | 内容 | 本文 | 付録 C の PR |
|---|---|---|---|
| 1 | 共通 bridge | §3, §4 | 02, 05 |
| 2 | 線形予測器 | §5 | 10, 11, 12 |
| 3 | Dudley の絶対値付き版 | §6, §7 | 07 |
| 4 | 公開 API と文書 | §13.6 | 17 |
| 5 | 標本依存 tail | §12.2 | 05, 06 |
| 6 | E2E 評価 | §12 | 06, 10, 12 |
| 7 | bridge の整理 | §13 | 03, 05, 06 |
| 8 | functional・reindex・有界差分 | §14 | 02, 03 |
| 9 | モジュール階層 | 実施しない（§0.5） | — |
| 10 | RKHS | §16 | 09, 13 |
| 11 | 明示的被覆数 | §17 | 08 |
| 12 | 損失・ERM・余剰誤差 | §18 | 14, 15, 16 |

## 10. 検証方針

各 phase で以下を実行する。

1. 変更した各ファイルを `lake env lean <file>` で個別に検査する。
2. `lake build` で `StatsMLlib` 全体を検査する。
3. `rg -n 'sorry|admit' StatsMLlib` で未完の証明が増えていないことを確認する。
4. `#check` または小さな利用例で、当該モジュールを直接 import しただけで新しい公開定理を適用できることを確認する。
5. 線形予測器の最終定理について、次を目視確認する。
   - 閾値の複雑度項が既存の経験評価の定数と一致する。
   - McDiarmid の指数部では関数値の一様上界 `X * W` または `Xinf * W` を使っている。
   - `0 < n` と正の半径条件が主張に明記されている。
6. Dudley について、片側版から絶対値付き版へ不等号を逆向きに使っていないことを確認する。
7. 新規モジュールが `ARCHITECTURE.md` の import 方向（tier）に違反していないことを確認する。

## 11. 想定される難所と対処

0. **Lean と Mathlib のバージョン差**

   上流は `leanprover/lean4:v4.27.0-rc1` と mathlib `master` で書かれており、
   StatsMLlib は `v4.33.0`（mathlib `v4.33.0` タグ）である。移植したコードは
   そのままでは通らない箇所があり、非推奨名、`Measure.real` 周辺、
   `ConditionallyCompleteLattice` の補題名、`gcongr`/`positivity` の挙動で差が出やすい。
   最初に移植する担当者が差分の対処法をまとめ、他の担当者へ共有する。

1. **`iSup` の上限有界性**

   符号対称化の等式では、`ℝ` 上の条件付き上限の補題が `BddAbove` を要求する。固定標本上の数値的な一様上界を補題の仮定に残し、無条件の書き換えとして証明しない。

2. **可分クラスの可積分性**

   非可算上限を直接可測としようとせず、既存の
   `empiricalRademacherComplexity_eq` と `RademacherComplexity_eq`
   により `denseSeq` 上の可算クラスへ還元する。

3. **`L1Ball`, `LinftyBall` の位相・可測構造**

   まず Euclidean space の部分型として既存 instance の推論を使う。推論できない性質だけを局所補題または instance として補い、型の定義自体は変更しない。

4. **`coveringNumber` が total boundedness の証明項を引数に持つこと**

   これは StatsMLlib では**部分的に解消済み**である（付録 B-1）。正準の
   `coveringNumber (eps) (s) : WithTop ℕ` は証明項を取らず、証明項を取る上流版は
   `coveringNumberNat (hs) (eps) : ℕ` に改名されている。新規補題は正準側で述べ、
   `coveringNumberNat` 版は `coe_coveringNumberNat` の系として出す。
   `signSymmetrization_totallyBounded` は `coveringNumberNat` を経由する箇所のために
   引き続き名前付き補題にし、各所で異なる匿名証明を生成しない。
   `coveringNumber` は `StatsMLlib/Analysis/MetricEntropy/` と
   `StatsMLlib/Statistics/Regression/LeastSquares/` からも参照されているため、
   定義や既存 API のシグネチャは変えないこと。

5. **`n = 0`**

   共通定義は `n = 0` でも保つが、平方根による具体評価と end-to-end の応用定理では `0 < n` を仮定する。`0⁻¹ = 0` に依存した見かけ上の自明化を応用 API へ露出させない。

6. **定数の二つの役割**

   経験複雑度の上界 `C` と、関数値の一様上界 `b` を混同しない。例えば $\ell_1$ 版では

   ```text
   C = (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
   b = Xinf * W
   ```

   であり、tail の閾値には `C`、指数部には `b` が現れる。

## 12. Phase 6 の詳細計画

### 12.1 今回の E2E の意味

今回 E2E と呼ぶ定理は、確率空間、データ確率変数、モデルの半径、標本サイズ、信頼度を仮定し、結論に期待 Rademacher 複雑度や未評価の経験 Rademacher 複雑度を残さない高確率一様偏差評価とする。

対象は次の二種類である。

1. **決定論的閾値版**

   全標本一様な経験複雑度上界を使う。既存の線形予測器の tail 定理がこの形に相当する。

2. **標本依存閾値版**

   観測標本上の二乗ノルム、座標ごとの二乗和、または Dudley entropy integral を閾値に残す。

この phase でいう E2E の終点は `uniformDeviation` とする。損失関数、ERM、余剰誤差まで含む評価には contraction inequality と risk/empirical-risk API が必要であり、別 phase とする。

### 12.2 先に追加する共通 bridge

§13.3 で追加する

```lean
uniform_deviation_tail_bound_separable_of_empirical_complexity
```

は閾値に経験 Rademacher 複雑度そのものを置く。一方、各モデルの E2E 定理では標本依存な上界

```lean
C : (Fin n → 𝒳) → ℝ
```

を代入したい。そこで、少なくとも可分クラスについて次の形の共通定理を
`StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` に追加する。

```lean
uniform_deviation_tail_bound_separable_of_sample_empirical_le
```

仮定:

```lean
∀ S, empiricalRademacherComplexity n F S ≤ C S
```

結論:

$$
\Pr\left\{
  \operatorname{UD}_n(F;S)
  \ge 2C(S)+3\varepsilon
\right\}
\le
2\exp\!\left(-\frac{n\varepsilon^2}{2b^2}\right).
$$

証明は経験複雑度を閾値にした既存定理と事象包含だけで行う。Dudley 専用定理に現在直接書かれている事象包含も、この共通 bridge へ置き換える。必要なら可算クラス版を先に証明し、可分クラス版を稠密可算化で導く。

### 12.3 信頼度 `δ` 形式

E2E の公開定理では `ε` を利用者に解かせず、$0<\delta\le1$ を受け取る形も用意する。
定義と実数計算は `StatsMLlib/Probability/Concentration/Confidence.lean`、
一様偏差への適用は `StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean` に置く。

決定論的閾値版では

$$
\varepsilon_\delta
=
b\sqrt{\frac{2\log(1/\delta)}{n}},
$$

標本依存閾値版では union bound の前係数 $2$ を吸収するため

$$
\widetilde\varepsilon_\delta
=
b\sqrt{\frac{2\log(2/\delta)}{n}}
$$

とする。したがって最終形はそれぞれ

$$
\Pr\left\{
  \operatorname{UD}_n\ge2C+\varepsilon_\delta
\right\}\le\delta
$$

および

$$
\Pr\left\{
  \operatorname{UD}_n\ge2C(S)+3\widetilde\varepsilon_\delta
\right\}\le\delta
$$

となる。指数関数と対数関数の変形、平方根の二乗、$\log(1/\delta)\ge0$ を共通補題へまとめ、モデルごとに再証明しない。

### 12.4 $\ell_2$ 線形予測器

`linear_predictor_l2_empirical_bound`（§5.1 で追加する）は各標本点のノルムを一様半径 $X$ で置き換えた後の評価だけを公開している。証明途中に現れている、より鋭い標本依存評価

$$
\widehat{\mathfrak R}_n(\mathcal F_{2,W};S)
\le
\frac{W}{n}
\sqrt{\sum_{k=1}^n\|S_k\|_2^2}
$$

を `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` に切り出す。

候補名:

```lean
linear_predictor_l2_empirical_bound_of_sample
```

既存の $XW/\sqrt n$ 評価は、$\|S_k\|_2\le X$ を使う系としてこの定理から導く。同じファイルに次の二つを E2E 評価として置く。

- 決定論的版:

  $$
  \Pr\left\{
    \operatorname{UD}_n
    \ge
    \frac{2XW}{\sqrt n}
    +XW\sqrt{\frac{2\log(1/\delta)}{n}}
  \right\}
  \le\delta.
  $$

- 標本依存版:

  $$
  \Pr\left\{
    \operatorname{UD}_n
    \ge
    \frac{2W}{n}
      \sqrt{\sum_k\|Z(\omega_k)\|_2^2}
    +3XW\sqrt{\frac{2\log(2/\delta)}{n}}
  \right\}
  \le\delta.
  $$

### 12.5 $\ell_1/\ell_\infty$ 線形予測器

既存証明では Massart の補題の後に、各座標の二乗和を一様上界 $X_\infty/\sqrt n$ で置き換えている。その直前を標本依存評価として切り出す。

標本依存量を

$$
Q_\infty(S)
=
\frac1n
\sup_{j<d}
\sqrt{\sum_{k=1}^n |S_{k,j}|^2}
$$

とし、

$$
\widehat{\mathfrak R}_n(\mathcal F_{1,W};S)
\le
WQ_\infty(S)\sqrt{2\log(2d)}
$$

を公開する。Lean では証明項を引数に持つ `Finset.sup'` を最終定理へ露出させず、`⨆ j : Fin d, ...` で定義する。有限型上の `iSup` と既存の `Finset.sup'` の一致が不足していれば補題を追加する。

候補名:

```lean
linear_predictor_l1_empirical_bound_of_sample
```

最終的な標本依存 E2E 評価は

$$
\Pr\left\{
  \operatorname{UD}_n
  \ge
  2WQ_\infty(S)\sqrt{2\log(2d)}
  +3X_\infty W
    \sqrt{\frac{2\log(2/\delta)}{n}}
\right\}
\le\delta
$$

とする。既存の決定論的評価も `δ` 形式の E2E corollary を追加する。

### 12.6 Dudley

`uniform_deviation_tail_bound_separable_of_dudley`（§7 で追加する）は entropy-form の E2E 評価だが、上流では事象包含を定理内で再証明している。そこで StatsMLlib では最初から 12.2 の標本依存 bridge を使う薄い corollary に整理する。

さらに

$$
\Pr\left\{
  \operatorname{UD}_n
  \ge
  2D_\alpha(S)
  +3b\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}
\le\delta
$$

という `δ` 形式を追加する。

具体的な数値だけからなる Dudley E2E 例には、Lipschitz 関数、RKHS、ニューラルネットワークなどの被覆数評価が別途必要である。この phase では新しいモデルの被覆数評価までは扱わず、観測標本上の entropy integral を残すところを Dudley 経路の E2E とする。

### 12.7 公開 example の構成

線形予測器の受け入れ example は、対応するモジュール末尾に次の順で置く。

1. 決定論的閾値の E2E tail。
2. 標本依存閾値の E2E tail。
3. 必要なら期待値版・期待 Rademacher 複雑度版。
4. 固定標本 wrapper。

既存の

```lean
linear_predictor_l2_bound
linear_predictor_l1_bound
```

は下位定理を再公開するだけなので、E2E の主例からは外す。ただし公開 API の互換性のため、この phase では削除せず、低水準 wrapper として残す。

最終定理の docstring には、複雑度項、集中項、確率上界を明記し、「経験評価」「期待評価」「高確率 E2E 評価」を区別する。

### 12.8 実装順と完了条件

実装順は次のとおりとする。

1. 標本依存 `C S` を受け取る共通 bridge。
2. `ε` 形式から `δ` 形式への共通変換。
3. $\ell_2$ の標本依存経験評価と、その一様版への系。
4. $\ell_2$ の二種類の E2E 定理。
5. $\ell_1/\ell_\infty$ の標本依存経験評価と、その一様版への系。
6. $\ell_1/\ell_\infty$ の二種類の E2E 定理。
7. Dudley 定理の共通 bridge 利用と `δ` 形式。
8. 受け入れ example の整備。`README.md` は PR 17、`FILE_TREE.md` は該当モジュールの PR。
9. `lake build`、未完証明検索、各モジュール単独 import からの `#check`。

完了条件は、各モデルの最終定理が次を満たすことである。

- 結論が標本分布に関する確率評価である。
- 閾値に未評価の `rademacherComplexity` または
  `empiricalRademacherComplexity` が残らない。
- 複雑度項と集中項が区別されている。
- 決定論的版と標本依存版の違いが theorem name と docstring から分かる。
- $n>0$, $0<\delta\le1$、正の半径など、平方根・対数・除算に必要な仮定が主張に現れる。

## 13. Phase 7: bridge の整理と汎化評価 API の再構成

### 13.1 目的

繰り返される次の変換を、再利用可能な bridge に集約する。

1. しきい値の上界による確率事象の包含。
2. 中心化 tail 評価と期待値評価から、非中心化 tail 評価を導く変換。
3. $\varepsilon$ 形式から $0<\delta\le1$ の信頼度形式への変換。
4. 可分な仮説クラスを可算稠密部分クラスへ制限する変換。

共通の順序・測度・実数計算だけに依存する補題は、`ForMathlib` 層ではなく
主題ディレクトリ（`StatsMLlib/Order/`, `StatsMLlib/Analysis/`,
`StatsMLlib/MeasureTheory/`, `StatsMLlib/Probability/Concentration/`）へ置く。
Rademacher 複雑度、汎化評価、個別モデルに依存する定理は
`StatsMLlib/LearningTheory/` の対応モジュールに置く。

### 13.2 汎用補題

- [ ] 実数値関数 $A\le B$ に対する superlevel 事象の単調性を
  `StatsMLlib/MeasureTheory/Measure/Real.lean` に追加する。
- [ ] 中心化 tail 評価と $\mathbb E[Y]\le C$ から
  $\Pr\{C+\varepsilon\le Y\}$ を評価する補題を同ファイルに追加する。
- [ ] 一般の前係数 $\kappa$ に対する信頼半径

  $$
  \operatorname{confidenceRadius}(\kappa,b,\delta,n)
  =
  b\sqrt{\frac{2\log(\kappa/\delta)}{n}}
  $$

  と指数関数の評価式を
  `StatsMLlib/Probability/Concentration/Confidence.lean` に追加する。

### 13.3 可算クラスの汎化評価

- [ ] 可算クラスの期待値評価、McDiarmid 評価、決定論的・標本依存しきい値の bridge を
  `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` に置く。
- [ ] `uniform_deviation_expectation_le_of_rademacher_le` を追加する。
- [ ] `uniform_deviation_tail_bound_countable_of_rademacher_le` を追加する。
- [ ] 既存の経験 Rademacher 複雑度上界版を上記 bridge の系として書き直す。
- [ ] 公開宣言名は原則として維持し、証明中の直接的な
  `measure_mono` と `linarith` の反復を除く。

> 上流は Phase 7 で `Generalization/Countable.lean` と `Generalization/Separable.lean` に
> ファイル分割したが、StatsMLlib は両方を `UniformDeviation/Bounds.lean` が持つ。
> 分割は行わない（付録 C-1）。

### 13.4 可分クラスへの制限

- [ ] 次の項を明示的に定義する。

  ```lean
  abbrev denseRestriction
      [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
      (F : H → α) : ℕ → α :=
    F ∘ denseSeq H
  ```

- [ ] 経験 Rademacher 複雑度、期待 Rademacher 複雑度、一様偏差の
  `denseRestriction` による不変性を個別の bridge として追加する。
  置き場と既存 `denseSeqInTB` との関係は付録 B-5 の決定に従う。
- [ ] 可測性・一様有界性の transfer 補題を追加する。
- [ ] 可分クラスの定理を `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` に置く。
- [ ] `RademacherComplexity_eq` などの命名を Mathlib の lowerCamelCase
  convention に合わせ、旧名には互換用 alias を残す。

### 13.5 信頼度形式と個別モデル

- [ ] `StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean` を作り、
  決定論的・標本依存しきい値の $\delta$ 形式を集約する。
- [ ] $\ell_2$ 線形予測器の期待評価・高確率評価を
  `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` に置く。
- [ ] $\ell_1/\ell_\infty$ 線形予測器の期待評価・高確率評価を
  `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` に置く。
- [ ] Dudley entropy integral と汎化評価の接続を
  `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` に置く。
- [ ] 繰り返される Dudley の右辺を、標本を引数に取る定義として一度だけ記述する。
      **付録 B-3 の決定に従う。** 公開 `def` にはせず、
      `LearningTheory/Rademacher/Dudley.lean` 内の `private noncomputable abbrev`
      に留める。entropy integral の正準は `Analysis.MetricEntropy` 側にあり、
      そこへ寄せるのは移植とは別 PR で行う。

### 13.6 受け入れ example

- [ ] 上流 `FoML/Main.lean` の各 `example` を、対応するモジュール末尾へ分散配置する。
      節と配置先の対応は次のとおり。

  | 上流 `Main.lean` の節 | example 数 | 配置先 |
  |---|---|---|
  | 一般の bridge | 1 | `LearningTheory/UniformDeviation/Bounds.lean` |
  | 観測経験複雑度 | 1 | `LearningTheory/UniformDeviation/Bounds.lean` |
  | $\ell_2$ 線形予測器 | 2 | `LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
  | $\ell_1/\ell_\infty$ 線形予測器 | 1 | `LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
  | 特徴写像 RKHS 予測器 | 2 | `LearningTheory/FunctionClass/KernelPredictor.lean` |
  | Dudley entropy integral | 3 | `LearningTheory/Rademacher/Dudley.lean` |
  | 近似 ERM と余剰誤差 | 3 | `LearningTheory/EmpiricalRiskMinimization/Generalization.lean` |

- [ ] `example` は各モジュールの末尾にまとめ、`/-! ## Examples -/` 見出しの下に置く。
- [ ] docstring では経験複雑度項・集中項・確率評価の役割を区別し、
  LaTeX 数式で最終評価を明記する。

### 13.7 今回の対象外

Mathlib の `Metric.coveringNumber` への移行は、値域が `ℕ` と `ℕ∞` で異なり、
開球・閉球の差もあるため、この phase では実施しない。独立した変更として
定理の対応関係を調査してから行う。

### 13.8 付随する cleanup

- [ ] `MassartNotation.r'`、`CoordIndex`、`coordSignedOn` など、参照されない
  定義を削除する。ただし StatsMLlib 内の他モジュールからの参照がないことを
  先に確認する。
- [ ] Massart の重複する非空性仮定と、最適化 tail 定理の未使用局所仮定を除く。
- [ ] Dudley の証明内部でのみ使う宣言を `private` にする。
- [ ] 実数に対する二倍の表記を `2 • C` から `2 * C` に統一する。

## 14. Phase 8: 共通 functional、reindex、有界差分の整理

### 14.1 対象

信頼半径の共通化（Phase 7 の 13.2）と `dudleyEntropyEstimate` は Phase 7 で実装するので、
この phase では公開 API と文書を再確認する。新規実装の中心は次の 4 点である。

1. McDiarmid の i.i.d. 積測度版に、全座標で同じ感度を使う wrapper を追加する。
2. 絶対値付き・片側 Rademacher 複雑度に共通する functional と PMF bridge を
   一度だけ記述する。
3. 仮説クラスの添字写像に対する reindex API を追加する。
4. 上限の差の評価と一標本置換の計算を共通補題へ分離し、
   `StatsMLlib/LearningTheory/UniformDeviation/BoundedDifference.lean` の重複を減らす。

### 14.2 McDiarmid の定数感度 wrapper

`StatsMLlib/Probability/Concentration/McDiarmid.lean` に追加する。

- [ ] `mcdiarmid_inequality_pos_iid_of_const` を追加する。
- [ ] `mcdiarmid_inequality_neg_iid_of_const` を追加する。
- [ ] `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` の一様偏差の上側 tail と
  経験 Rademacher 複雑度の下側 tail をこの wrapper から導く。

wrapper は定数関数 `fun _ ↦ c` を公開定理の結論へ露出させず、

$$
t\,|\iota|\,c^2\le1
$$

を仮定として受け取る。これにより `∑ i, (c i)^2` の同じ簡約を各応用で
繰り返さない。

なお StatsMLlib の `McDiarmid.lean` には現在 `mcdiarmid_inequality_pos`,
`mcdiarmid_inequality_pos'`, `mcdiarmid_inequality_pos_of_sum_sq_pos`,
`mcdiarmid_inequality_neg` があり、i.i.d. 積測度版は入っていない。
上流の i.i.d. wrapper もあわせて移植する。

### 14.3 Rademacher functional と PMF bridge

`StatsMLlib/LearningTheory/Rademacher/Signs.lean` に追加する。

- [ ] 正規化符号和 `normalizedRademacherSum` を追加する。
- [ ] 後処理関数 `φ : ℝ → ℝ` を受け取る
  `empiricalRademacherFunctional` を追加する。
- [ ] 有限平均版と `signVecPMF` による積分版の一致を一般の `φ` について示す。
- [ ] 絶対値付き版は `φ = abs`、片側版は `φ = id` の系として既存 API を保つ。

定義は型だけでなく項まで次の形で公開する。

```lean
normalizedRademacherSum n F S σ h
  = (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k)

empiricalRademacherFunctional n φ F S
  = (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ h, φ (normalizedRademacherSum n F S σ h)
```

### 14.4 仮説添字の reindex API

`StatsMLlib/LearningTheory/Rademacher/Reindex.lean` を新設する。

- [ ] 任意の写像 `e : G → H` による経験 Rademacher 複雑度の単調性を追加する。
- [ ] `e` が全射なら、絶対値付き・片側経験 Rademacher 複雑度が不変であることを
  追加する。
- [ ] 全射 reindex に対する期待 Rademacher 複雑度と一様偏差の不変性を追加する。
- [ ] `denseRestriction` は位相的稠密性を使う別の bridge として維持し、
  単なる全射 reindex と混同しない。

このモジュールは `Rademacher/Complexity.lean`、`Analysis/FiniteSample.lean`、
`Order/IndexedSupremum.lean` を import する。

### 14.5 有界差分の共通補題

- [ ] 点ごとの距離評価から二つの実数値 `iSup` の距離評価を得る補題を
  `StatsMLlib/Order/IndexedSupremum.lean` に追加する。
- [ ] 正規化標本平均の一標本置換評価を
  `StatsMLlib/Analysis/FiniteSample.lean` に追加する。
- [ ] `uniformDeviation_bounded_difference` と
  `empiricalRademacherComplexity_bounded_difference` をこれらの補題で整理する。

### 14.6 受け入れ example と文書

- [ ] 可分・高確率・経験 Rademacher 複雑度を同時に使う基本定理

  $$
  \Pr\left\{
    \operatorname{UD}_n(F;S)
    \ge 2\widehat{\mathfrak R}_n(F;S)+3\varepsilon
  \right\}
  \le
  2\exp\left(-\frac{n\varepsilon^2}{2b^2}\right)
  $$

  を `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` の主要 example として掲載する。
- [ ] （PR 17 でまとめて）`README.md` の定義、bridge、公開 API を更新する。
- [ ] `lake build`、未完証明検索、各モジュール単独 import からの `#check` を行う。

## 16. Phase 10: RKHS の Rademacher 複雑度

### 16.1 目標と参考文献

Mohri, Rostamizadeh, Talwalkar, *Foundations of Machine Learning*,
Theorem 6.12（印刷ページ 118）を形式化する。
実装目標は、実 Hilbert 空間 $\mathcal H$、
特徴写像 $\Phi:\mathcal X\to\mathcal H$、重み半径 $\Lambda\ge0$ に対して

$$
\widehat{\mathfrak R}_n
\left(
  \left\{x\mapsto\langle w,\Phi(x)\rangle:
    \lVert w\rVert_{\mathcal H}\le\Lambda
  \right\};S
\right)
\le
\frac{\Lambda}{n}
\sqrt{\sum_{k=1}^n K(S_k,S_k)}
$$

を示すことである。ただし

$$
K(x,y)=\langle\Phi(x),\Phi(y)\rangle.
$$

$K(x,x)\le r^2$ なら

$$
\widehat{\mathfrak R}_n\le\frac{r\Lambda}{\sqrt n}
$$

を系として得る。本リポジトリの経験 Rademacher 複雑度は上限の内側に絶対値を
持つが、重み球が $w\mapsto-w$ で閉じているため Mohri の片側定義と同じ評価になる。

参考文献の PDF はリポジトリに含めない。書誌情報は docstring に記載する。

### 16.2 実装方針

Mathlib には直接利用できる一般 RKHS 構造がないため、先に特徴写像による
Hilbert 空間版を実装し、その後で kernel 表記を与える。

1. `StatsMLlib/LearningTheory/FunctionClass/HilbertPredictor.lean`
   - 一般の実内積空間上の
     `hilbertPredictor w x = ⟪w, x⟫` を定義する。
   - 現在の有限次元 `LinearPredictor/L2.lean` の証明から、次元に依存しない
     Rademacher 符号和の二乗平均評価を切り出す。
   - 閉球全体について

     $$
     \widehat{\mathfrak R}_n
     \le
     \frac{\Lambda}{n}
       \sqrt{\sum_k\lVert \Phi(S_k)\rVert^2}
     $$

     を示す。
2. `StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean`
   - `kernelOfFeatureMap Φ x y = ⟪Φ x, Φ y⟫` を項まで定義する。
   - 対角値
     `kernelOfFeatureMap Φ x x = ‖Φ x‖ ^ 2` を示す。
   - `kernelTrace Φ S = ∑ k, kernelOfFeatureMap Φ (S k) (S k)` を定義する。
   - trace 版と一様対角上界 $K(x,x)\le r^2$ 版を公開する。
3. 同じ `KernelPredictor.lean` の後半
   - 特徴写像の可測性、重み変数についての連続性、Hilbert 空間の可分性を仮定し、
     期待 Rademacher 複雑度、期待一様偏差、高確率評価へ接続する。
   - 観測標本の kernel trace を残す標本依存 E2E 評価と、
     $r\Lambda/\sqrt n$ を使う決定論的 E2E 評価を用意する。
   - trace 版と一様対角上界版を受け入れ `example` として末尾に置く。

上流は 2 と 3 を `Model/RKHS.lean` と `Generalization/RKHS.lean` に分けているが、
StatsMLlib は `LinearPredictor/L1.lean`, `L2.lean` と同様に 1 ファイルにまとめる。
行数が過大になる場合のみ `FunctionClass/KernelPredictor/Basic.lean` と
`FunctionClass/KernelPredictor/Generalization.lean` へ分割する。

### 16.3 設計上の注意

- [ ] 最初の定理は「任意の PDS kernel から RKHS を構成する」定理ではなく、
  与えられた特徴写像から誘導される kernel を扱う。
- [ ] PDS 性は有限 Gram 行列の二次形式が非負である形で別補題にする。
- [ ] 完備性が証明に不要な固定標本評価では `InnerProductSpace ℝ H` まで仮定を弱め、
  RKHS と呼ぶ公開 wrapper では `CompleteSpace H` を仮定する。
- [ ] 可分クラスの汎化評価へ進む定理だけに `SeparableSpace H` を要求する。
- [ ] 既存の $\ell_2$ 線形予測器を一般 Hilbert 空間定理の有限次元系として整理する。

### 16.4 完了条件

- [ ] kernel trace 版と $r\Lambda/\sqrt n$ 版がある。
- [ ] 固定標本、期待量、標本依存 tail、決定論的 tail が接続されている。
- [ ] Mohri Theorem 6.12 の各仮定と Lean の仮定の対応が docstring に記載されている。
- [ ] RKHS の E2E `example` が少なくとも 2 本ある。

## 17. Phase 11: 具体的被覆数による Dudley 評価

### 17.1 第一段階: 有限仮説クラス

`StatsMLlib/LearningTheory/Rademacher/FiniteClass.lean` を新設する。

まず、有限型 $H$ で添字付けられたクラスについて

$$
N(F,\varepsilon)\le |H|
$$

を示す。符号対称化後は

$$
N(F^\pm,\varepsilon)\le 2|H|
$$

となる。これを Dudley の積分へ代入し、$\alpha>0$ に対して

$$
\widehat{\mathfrak R}_n(F;S)
\le
4\alpha+
\frac{12}{\sqrt n}
\left(\frac c2-\alpha\right)
\sqrt{\log(2|H|)}
$$

という被覆数を含まない評価を得る。

- [ ] 有限型全体を中心集合に取る `coveringNumber_le_fintype_card` を
  `StatsMLlib/Topology/MetricSpace/CoveringNumber/Basic.lean` に追加する。
- [ ] `EmpiricalFunctionSpace F S` の有限型 instance と card の評価を
  `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean` に追加する。
- [ ] 符号対称化後の card $2|H|$ を使う Dudley corollary を `FiniteClass.lean` に追加する。
- [ ] 明示的な $\alpha$ を代入した高確率汎化評価を同ファイルに追加し、
  受け入れ `example` を末尾に置く。

### 17.2 第二段階: 一次元 Lipschitz パラメータ族

`StatsMLlib/LearningTheory/Rademacher/LipschitzParameter.lean` を新設する。

有限クラスだけでなく、$t\in[-W,W]$ で添字付けられ、

$$
|F_t(x)-F_s(x)|\le L|t-s|
$$

を満たすクラスを扱う。等間隔 grid により

$$
N(F,\varepsilon)
\le
\left\lceil\frac{2WL}{\varepsilon}\right\rceil+1
$$

を示す。Dudley 積分全体を特殊関数で厳密計算する代わりに、
被覆数の反単調性を使って

$$
\int_\alpha^{c/2}\sqrt{\log N(F,x)}\,dx
\le
\left(\frac c2-\alpha\right)
\sqrt{\log N(F,\alpha)}
$$

と評価し、右辺へ grid の card 上界を代入する。

- [ ] 閉区間の有限等間隔 grid と cover 補題を追加する。
      経験距離に依存しない純粋な区間 grid の部分の置き場は
      `StatsMLlib/Analysis/NormedSpace/CoveringNumber/`（既に
      `coveringNumber_euclideanBall_le` と `coveringNumber_l1Ball_le` がある）。
      そもそも独立に書く必要があるかは付録 B-4 を参照。経験距離を使う部分は
      import 方向の制約から `LearningTheory/Rademacher/LipschitzParameter.lean` に置く。
- [ ] パラメータ Lipschitz 性から経験距離 Lipschitz 性への bridge を追加する。
- [ ] 被覆数の明示式、Dudley 評価、高確率汎化評価まで接続する。

### 17.3 完了条件

- [ ] 受け入れ `example` の最終式に未評価の `coveringNumber` が残らない。
- [ ] 有限クラスと連続パラメータ族の少なくとも二例を用意する。
- [ ] proof term を引数に取る既存 `coveringNumber` API は内部に隠す。

## 18. Phase 12: 損失関数、ERM、余剰誤差

### 18.1 中心定義

`StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Defs.lean` を作り、データ型 $\mathcal Z$ と仮説型 $H$ に対して
次を項まで定義する。

```lean
def populationRisk
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵) (h : H) : ℝ :=
  ∫ ω, ℓ h (Z ω) ∂μ

def empiricalRisk
    (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (h : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ h (S k)

def excessRisk
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵)
    (h hstar : H) : ℝ :=
  populationRisk ℓ μ Z h - populationRisk ℓ μ Z hstar
```

厳密 ERM と $\eta$-近似 ERM は、最初から `argmin` を選択するのではなく
述語として定義する。

```lean
def IsERM (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h

def IsApproxERM
    (η : ℝ) (n : ℕ) (ℓ : H → 𝒵 → ℝ)
    (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h + η
```

`StatsMLlib/Statistics/Regression/LeastSquares/Defs.lean:75` に二乗損失へ特殊化した
ERM 述語 `isLeastSquaresEstimator` が既にある。付録 B-6 の方針に従い、ここでは一般形を
新設し、`isLeastSquaresEstimator` はそのまま残したうえで橋渡し補題を 1 本用意する。

### 18.2 決定論的 oracle inequality

`StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Basic.lean` に置く。

- [ ] `uniformDeviation` が risk と empirical risk の差の上限に定義上等しいことを示す。
- [ ] `hhat` が ERM なら任意の比較対象 `hstar` に対し

  $$
  R(h_{\rm ERM})-R(h^\star)
  \le 2\operatorname{UD}_n
  $$

  を示す。
- [ ] $\eta$-近似 ERM について

  $$
  R(\widehat h)-R(h^\star)
  \le 2\operatorname{UD}_n+\eta
  $$

  を示す。
- [ ] 真の risk minimizer の存在は、コンパクト性と risk の連続性を仮定する
  別モジュールに分ける。（上流でも未実施）

### 18.3 損失クラスと contraction

予測関数 $F_h:\mathcal X\to\mathbb R$ とラベル付きデータ
$z=(x,y)$ に対し、損失クラス

$$
z\mapsto \ell(F_h(x),y)
$$

を定義する。contraction は
`StatsMLlib/LearningTheory/Rademacher/Contraction.lean` に置く。

- [ ] 有界損失を直接関数クラスとして既存の汎化定理へ渡す bridge を先に実装する。
- [ ] 各 $y$ について $u\mapsto\ell(u,y)$ が $L$-Lipschitz である場合の
  Rademacher contraction inequality を追加する。
- [ ] $\ell(0,y)\ne0$ の場合は中心化した損失へ書き換える補題を用意する。
- [ ] contraction の定数が絶対値付き定義と片側定義で異ならないかを明示的に検証する。

上流の contraction は有限仮説型について完全に証明されている。片側定義の定数は
$L$、本リポジトリの絶対値付き定義の定数は $2L$ である。一般の可分クラスへの
拡張は有限近似または別の contraction bridge として切り分ける。

### 18.4 高確率の余剰誤差評価

`StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Generalization.lean` に置く。
既存の一様偏差評価と oracle inequality を合成し、例えば期待 Rademacher 複雑度版

$$
\Pr\left\{
  R(\widehat h)-R(h^\star)
  \ge
  4\mathfrak R_n(\ell\circ F)+2\varepsilon+\eta
\right\}
\le
\exp\left(-\frac{n\varepsilon^2}{2b^2}\right)
$$

および観測標本の経験 Rademacher 複雑度版

$$
\Pr\left\{
  R(\widehat h)-R(h^\star)
  \ge
  4\widehat{\mathfrak R}_n(\ell\circ F;S)+6\varepsilon+\eta
\right\}
\le
2\exp\left(-\frac{n\varepsilon^2}{2b^2}\right)
$$

を示す。ここで $b$ は損失値の絶対値上界である。

- [ ] 標本依存学習則 `A : (Fin n → 𝒵) → H` と点ごとの
  `IsApproxERM η ℓ S (A S)` を受け取る定理を追加する。
- [ ] 信頼度 $\delta$ 形式を追加する。
- [ ] RKHS と Lipschitz loss を contraction で接続した E2E 例を
  `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/KernelPredictor.lean` に追加する。
- [ ] ERM の主要な利用例を `EmpiricalRiskMinimization/Generalization.lean` 末尾の `example` として掲載する。

`EmpiricalRiskMinimization/KernelPredictor.lean` は Phase 10 の `FunctionClass/KernelPredictor.lean` と Phase 12 の
`EmpiricalRiskMinimization/Generalization.lean`、`Rademacher/Contraction.lean`、
`Rademacher/Reindex.lean` の 4 本すべてを import する。作業を分担する場合、
ここが唯一の phase 間依存になる。

### 18.5 実装順

1. risk、empirical risk、余剰誤差、ERM 述語。
2. 決定論的 oracle inequality。
3. 有界損失クラスを既存 bridge へ渡す高確率定理。
4. contraction inequality。
5. $\eta$-近似 ERM と信頼度形式。
6. RKHS または線形予測器との E2E 接続。

### 18.6 完了条件

- [ ] 最終定理の結論が `uniformDeviation` ではなく余剰誤差になっている。
- [ ] 学習則の measurability と argmin の存在を、不要な定理へ過剰に要求しない。
- [ ] exact ERM と approximate ERM の両方を扱う。
- [ ] 決定論的 oracle inequality、Rademacher 評価、contraction、tail 評価が
  個別の bridge として再利用できる。

---

## 付録 B. 重複への対処（結論）

上流 `origin/main` の 466 宣言と StatsMLlib の全宣言を突き合わせ、未移植 203 本を主題別に
確認した結果の結論。

| | 重複 | 実装時にすること |
|---|---|---|
| B-1 | `coveringNumber` が上流と StatsMLlib で別物 | 正準は `coveringNumber (eps) (s) : WithTop ℕ`。証明項を取る上流版は `coveringNumberNat`。新規補題は正準側で述べ、`coe_coveringNumberNat` で `coveringNumberNat` 版を導く。上流の証明は貼れない（§11-4） |
| B-2 | 有限クラスの `√log card` | `coveringNumber_le_card`, `sqrtEntropy_le_sqrt_log_card`, `exists_optimal_enet` で賄える。`coveringNumber_le_fintype_card` は `Finset.univ` を渡すだけ。上流の `Nat.find` 証明は移植しない（§17.1） |
| B-3 | entropy integral が 3 系統 | **正準は `Analysis.MetricEntropy`。** 移植中は新しい定義を作らず、Dudley の右辺は `private noncomputable abbrev` に留める（§13.5）。一本化は PR 18 |
| B-4 | 明示的被覆数 | `coveringNumber_euclideanBall_le`, `coveringNumber_l1Ball_le` が既にある。1 次元 grid を `LearningTheory/` に新設しない（§17.2） |
| B-5 | 稠密可算化 bridge が 2 系統 | `denseRestriction` を正準にし、`denseSeqInTB` は残したまま橋渡し補題 1 本で系にする。手順は下記 |
| B-6 | ERM 述語が 2 つ | `IsERM` を一般形として新設し、`isLeastSquaresEstimator` は残す。`isLeastSquaresEstimator → IsERM` の bridge を 1 本（§18.1） |
| B-8 | maximal inequality が 3 系統 | 移植中は触らない。PR 19 で扱う |

**重複が無いことを確認済み**（再調査不要）: 信頼度 14 宣言（`confidence` の出現 0 件）、
`measureReal_superlevel_*`（`superlevel` 0 件）、McDiarmid の i.i.d. 版 3 本、
`abs_normalized_fin_sum_*`、`ciSup_comp_of_surjective`、RKHS 系。
`abs_ciSup_sub_ciSup_le` も既存には無いが、`UniformDeviation/BoundedDifference.lean` が
同じ議論を `:125`–`:164` と `:206`–`:245` でインライン展開しているので、§14.5 は
新規 API ではなく既存証明のリファクタになる。

### B-3 の手順

**段階 1（移植中）**

- [ ] 積分部分は既存の `dudley_entropy_integral_bound` と同じ
      `∫ x in ε..c/2, √(Real.log (coveringNumberNat h' x))` の形で書く。
- [ ] 係数部分は `LearningTheory/Rademacher/Dudley.lean` 内の
      `private noncomputable abbrev` に留め、公開 API にしない。

**段階 2（PR 18）**

`metricEntropyOfNat n = if n ≤ 1 then 0 else Real.log n` は、Lean では
`Real.log 0 = Real.log 1 = 0` なので全ての `n` で `Real.log n` に等しい。よって全有界な `s` と
`eps > 0` について `metricEntropy eps s = Real.log (coveringNumberNat hs eps)` が
`coe_coveringNumberNat` からほぼ定義的に出る。残りは lintegral(`Ioc`) と intervalIntegral の
変換だけで、可積分性は `dudleyIntegrand_anti_eps_of_totallyBounded` と
`entropyIntegralENNRealTrunc_lt_top` から出る。30〜60 行の見込み。

- [ ] (a) `entropyIntegralTrunc (Set.univ : Set (EmpiricalFunctionSpace F S)) ε (c / 2)
      = ∫ x in ε..c/2, √(Real.log (coveringNumberNat h' x))`（等式）
- [ ] (b) `entropyIntegralTrunc T δ D ≤ dudleyEntropyIntegral T δ D`（内部ネットと外部ネットの差があるので不等式）
- [ ] `ARCHITECTURE.md` の Import direction に所有権を 1 行追記する。

**やってはいけないこと**

- `dudley_entropy_integral'`（`Rademacher/Dudley.lean:1528`）の主張を書き換える。
  ファイル 1,600 行のほぼ全部があの定理の補助なので、証明が壊れる。段階 2 は corollary の追加だけ。
- `subsetENetCard` を消して `coveringNumber` に統一する。内部ネットは chaining の構成に本質的。
- 上流の `dudleyEntropyEstimate` を公開 `def` にする。4 つ目になる。

### B-5 の手順

Mathlib の `denseSeq [SeparableSpace α] [Nonempty α]` は、`SeparableSpace` が
`class SeparableSpace : Prop`（`Mathlib/Topology/Bases.lean:333`）、`Nonempty` も Prop クラスなので、
proof irrelevance によりどのインスタンスを渡しても同じ項になる。したがって `denseSeqInTB` の
`letI` で入れたインスタンスと `denseRestriction` が文脈から取るインスタンスは一致する。

- [ ] `denseRestriction` と周辺補題を `StatsMLlib/Topology/SeparableSpace/Supremum.lean` に追加し、
      正準形 `separableSpaceSup_eq_denseRestriction : (⨆ h, F h) = ⨆ n, denseRestriction F n` を出す。
- [ ] `Probability/Process/Dudley.lean` に橋渡し補題
      `fun n ↦ f (denseSeqInTB hs hsne n) = denseRestriction f` を 1 本置く。
- [ ] `sup_subtype_eq_iSup_denseSeq` を `separableSpaceSup_eq_denseRestriction` の系に書き直す。
      `sup_over_s_eq_iSup_denseSeq_pathwise` はその各点版なので自動的に従う。
- [ ] 使用箇所 7 か所（`Probability/Process/Dudley.lean` の `:1026`, `:1043`, `:1044`, `:2533`,
      `:2536`, `:2539`, `:2544`）は `denseSeqInTB` のまま残す。**削除しない。**

## 付録 C. PR の順序

### C-1. 方針

- **1 PR = 1 ブランチ**（`reflect/NN-<topic>`）、base は `main`。前の PR が未マージのうちは
  base を前のブランチにする（stacked PR）。マージ時に GitHub が base を `main` へ自動で
  付け替える。レビューが付いた後の force-push は避け、`main` の取り込みは `git merge main` で行う。
- **各 PR は単体で `lake build` が緑、`sorry` / `admit` / `axiom` / `native_decide` ゼロ。**
  `sorry` を残して次の PR に持ち越さない。証明が長い場合は主張の group で切り、証明の途中では切らない。
- **追加と、既存の動いている証明のリファクタを混ぜない。** リファクタを含む PR には
  「宣言の追加・削除ゼロ」と明記する。
- **1 PR あたり 200〜600 行 / 10〜20 宣言**を目安にする。Lean ではビルドが通れば主張の証明は
  機械的に保証されるので、レビューの実質的な対象は宣言数と設計判断であり行数ではない。
  PR 本文には新規公開宣言の一覧と、「上流の証明をそのまま移した部分」「Lean 4.27→4.33 の
  差分で書き直した部分」の区別を書く。後者だけ読めば済むようにする。
- **文書の更新**は、モジュールを追加した PR の中で `FILE_TREE.md` も一緒に更新する
  `README.md` の整理だけ PR 17 にまとめる。
- **`note/` は `main` にマージしない**（§C-2）。恒久的な結論は `ARCHITECTURE.md` /
  `FILE_TREE.md` / `README.md` へ移す。

**`UniformDeviation/Bounds.lean` は分割しない。** 上流は Phase 7 で可算・可分・信頼度形式を
3 ファイルに分けたが、分割 PR を先に挟むと既存 import の書き換えで着手が遅れる。§4・§12.2・§13.3・
§13.4・§14.2・§14.6 の追記が全部このファイルに来るので、運用で衝突を避ける。

- [ ] `Bounds.lean` への追記は PR 05 に集約する。§13.3 の可算・可分は同じ PR で入れる。
- [ ] 追記は必ずファイル末尾に足し、既存宣言の順序を入れ替えない。§13.3 の「既存版を bridge の系に
      書き直す」は、他の追記が全部入ってから最後に行う。
- [ ] 信頼度形式は最初から `UniformDeviation/Confidence.lean`（§13.5）に書き、`Bounds.lean` に入れない。

**`example` はライブラリ本体に置く。** `lakefile.lean` の target は `lean_lib «StatsMLlib»` 一つで
テスト target が無く、`test/` も無く、ライブラリ全体で行頭 `example` は 0 件である。それでも
`test/` を新設せず本体に置く。target と CI を増やさずに済み、doc-gen4 の出力にも載って、上流
`Main.lean` が持っていた「主要定理の使い方の索引」という価値を保てるため。配置は §13.6 の表に従う。

### C-2. 着手前

**`note/` は `main` にマージしない。**

`FILE_TREE.md` が宣言しているとおり、このリポジトリが持つのは公開 Lean ソースツリーと
恒久的なプロジェクト方針の文書（`ARCHITECTURE.md`, `AUTHORS.md`, `CODE_OF_CONDUCT.md`,
`CONTRIBUTING.md`, `LICENSE`, `README.md`, `FILE_TREE.md`）だけである。移植作業の計画書は
そこに並ぶ種類のものではなく、作業が終われば大半が陳腐化する。
`note/upstream/` に至っては別プロジェクトの内部文書 133KB で、このリポジトリに存在しない
`FoML/...` というモジュール名で書かれている。

この文書のうち恒久的に必要な結論には、それぞれ行き先がある。

| 結論 | 行き先 | PR |
|---|---|---|
| layer-one `Order` の追加 | `ARCHITECTURE.md` | 01 |
| `LearningTheory/EmpiricalRiskMinimization/` の追加 | `ARCHITECTURE.md` | 14 |
| 新規 15 モジュールの位置 | `FILE_TREE.md` | 各モジュールの PR |
| entropy integral の所有権は `Analysis.MetricEntropy`（B-3） | `ARCHITECTURE.md` の Import direction | 18 |
| `coveringNumber` の正準は証明項を取らない方（B-1） | 同上 | 18 |
| 公開 API 一覧 | `README.md` | 17 |

**手順 0 — issue と計画ブランチ** ★設計方針

- [ ] `CONTRIBUTING.md` が求めるとおり issue を立てる。本文には §0.0 の目的、§0.3 の対応表、
      付録 B の設計判断、この付録 C の PR 一覧を要約して書く。
      文書全体は 101,896 バイトあり GitHub の issue 本文上限（65,536 文字）を超えるので、全文は貼らない。
- [ ] `note/` を `reflect/plan` ブランチに push し、issue からリンクする。
      **このブランチはマージしない。** インラインでコメントを受けたい場合は、そこから
      draft PR を開いてマージせずに閉じる。その場合は「マージしない PR」であることを本文に明記する。
- [ ] ファイルヘッダの著者表示の方針（§C-5）を issue で決める。
- [ ] 以降の PR は `note/` を含めない。計画のチェックボックスの更新は `reflect/plan` ブランチ上で行う。

**spike（マージしない）**

`Order/IndexedSupremum` → `Signs` の `empiricalRademacherComplexity_comp` →
`Complexity` の `rademacherComplexity_le_of_empirical_le` → `Bounds` の可算クラス版 →
`LinearPredictor/L2` の決定論的 tail、を証明を雑にしてでも一度通す。
Lean 4.27→4.33 の mathlib 差分がどこで刺さるか（§11-0）と、
§3.2・§4・§12.2・§12.3 の主張の形が正しいかをここで確認して捨てる。

### C-3. 本番の順序

行数は上流 `origin/main` から移す新規 Lean の見積り、宣言数は移植対象 204 の内訳。
★ は設計方針に触れるので PR ごとに議論する回。

#### 基盤（順番に積む）

| # | 対象 | 上流 | 行 | 宣言 | 依存 |
|---|---|---|---|---|---|
| 01 ★ | `Order/IndexedSupremum.lean`, `Analysis/FiniteSample.lean`, `MeasureTheory/Measure/Real.lean`, `Probability/Concentration/Confidence.lean`（すべて新規）＋ `ARCHITECTURE.md` に layer-one `Order` を追記 | `ForMathlib/{Order.ISup, Analysis.FiniteSample, MeasureTheory.Measure.Real, Probability.Confidence}` | 160 | 8 | — |
| 02 | `Rademacher/{Defs,Signs,Complexity}.lean`, `Probability/Concentration/McDiarmid.lean` | `Defs`, `Rademacher.Signs`, `Rademacher.Expectation`, `Probability.McDiarmid` | 384 | 23 | 01 |
| 03 ★ | `Rademacher/Reindex.lean`（新規）＋ `UniformDeviation/BoundedDifference.lean` ＋ **§14.5 リファクタ**（`ciSup` の共通化。宣言の追加・削除ゼロ） | `Rademacher.Reindex`, `Rademacher.BoundedDifference` | 158 | 7 | 01, 02 |
| 04 | `EmpiricalProcess/{Metric,FunctionClass}.lean`, `Topology/MetricSpace/CoveringNumber/Basic.lean` | `Entropy.PseudoMetric`, `Entropy.CoveringNumber` | 137 | 11 | 01, 02 |
| 05 ★ | `UniformDeviation/Bounds.lean`（可算＋可分）、`Topology/SeparableSpace/Supremum.lean` に `denseRestriction` ＋ **B-5 リファクタ**（`denseSeqInTB` を系にする） | `Generalization.{Countable,Separable}`, `ForMathlib.Topology.SeparableSpace` | 495 | 22 | 01, 03 |
| 06 | `UniformDeviation/Confidence.lean`（新規、δ 形式） | `Generalization.Confidence` | 211 | 12 | 05 |

06 まで通ると、任意の固定標本一様評価を汎化評価へ投入する経路が揃う。
以降の 07〜16 は互いに独立なので、順番を入れ替えてよい。

#### 枝

| # | 対象 | 上流 | 行 | 宣言 | 依存 |
|---|---|---|---|---|---|
| 07 | `Rademacher/Dudley.lean`（絶対値付き版と汎化接続。§13.5 の右辺は `private abbrev` に留める — B-3 段階 1） | `Entropy.Dudley`, `Generalization.Dudley` | 357 | 17 | 04, 06 |
| 08 | `Rademacher/FiniteClass.lean`, `Rademacher/LipschitzParameter.lean`（ともに新規） | `Entropy.{FiniteClass,LipschitzParameter}`, `Generalization.{FiniteClass,LipschitzParameter}` | 564 | 17 | 07 |
| 09 | `FunctionClass/HilbertPredictor.lean`（新規） | `Model.HilbertPredictor` | 256 | 7 | 02 |
| 10 | `FunctionClass/LinearPredictor/L2.lean` | `Model.LinearPredictorL2`, `Generalization.LinearPredictorL2` | 279 | 11 | 03, 06, 09 |
| 11 | `FunctionClass/LinearPredictor/L1.lean`（固定標本評価まで） | `Model.LinearPredictorL1` | 444 | 11 | 02 |
| 12 | `FunctionClass/LinearPredictor/L1.lean`（汎化評価） | `Generalization.LinearPredictorL1` | 166 | 5 | 06, 11 |
| 13 | `FunctionClass/KernelPredictor.lean`（新規） | `Model.RKHS`, `Generalization.RKHS` | 292 | 16 | 06, 09 |
| 14 | `EmpiricalRiskMinimization/{Defs,Basic}.lean`（新規）＋ **B-6 の bridge**（`isLeastSquaresEstimator` → `IsERM`） | `Learning.{Defs,ERM}` | 242 | 22 | 02 |
| 15 | `Rademacher/Contraction.lean`（新規） | `Learning.Contraction` | 487 | 8 | 02, 14 |
| 16 | `EmpiricalRiskMinimization/{Generalization,KernelPredictor}.lean`（新規） | `Generalization.{Learning,RKHSLearning}` | 339 | 7 | 03, 06, 13, 14, 15 |

**09 は 10 より先**。上流 `Model/LinearPredictorL2.lean` が `Model.HilbertPredictor` を
import しており、$\ell_2$ の評価は Hilbert 空間版の有限次元系として書くため。

#### 仕上げ

| # | 対象 |
|---|---|
| 17 | 受け入れ `example` 13 本（§13.6 の表のとおり各モジュール末尾へ）＋ `README.md` の公開 API 表 |

ここまでで移植分 204 宣言・約 4,971 行。

#### 重複解消（§0.0 の目的 2）

| # | 対象 |
|---|---|
| 18 ★ | **B-3 段階 2。** `entropyIntegralTrunc` と FoML 系・`TruncatedDudley` 系をつなぐ橋渡し補題 2 本を追加し、`Rademacher/Dudley.lean` の公開評価を正準形で述べ直す corollary を出す。`dudley_entropy_integral'` の主張は変えない。`ARCHITECTURE.md` に所有権の 1 行を追記する |
| 19 ★ | **B-8。** `Probability/Concentration/Maximal.lean`、`Probability/Process/FiniteMaximum.lean`、`Probability/Process/SubGaussian.lean` の maximal inequality 3 系統の関係を明示するか、一方を他方の系にする。方針は PR で提案して議論する |

### C-4. PR ごとに議論する回

着手前の issue と、付録 C-3 で ★ を付けた 5 本だけが、ライブラリの設計方針に触れる。

| # | 議論する内容 |
|---|---|
| 手順 0（issue） | 全体の設計判断（§0.3 の対応表、§0.4 の命名、付録 B・C-1）と、ファイルヘッダの著者表示 |
| 01 | layer-one に `Order` を追加してよいか（`ARCHITECTURE.md` の layer 表・構成図・import 方向図が変わる） |
| 03 | `UniformDeviation/BoundedDifference.lean` の既存証明を書き換える |
| 05 | `Probability/Process/Dudley.lean` の `denseSeqInTB` 周りを書き換える |
| 18 | entropy integral の所有権を `Analysis.MetricEntropy` に一本化する |
| 19 | maximal inequality 3 系統の扱い |

残る 14 本は新規ファイルの追加か、既存ファイルへの純粋な追記である。

### C-5. 著者表示

`AUTHORS.md` が次を要求している。

> Existing notices must be preserved when code is moved, renamed, or substantially reused.
> migrated source headers must not be inferred from commit authors alone.

現状は次のとおり。

- 移植対象（上流 `3819e1e` 以降）のコミットは、上流の git 履歴上すべて Sho Sonoda 氏による。
- 上流 `lean-rademacher` にはファイルヘッダがほぼ無い（`Authors:` 行を持つのは
  `FoML/Probability/Hoeffding.lean` の 1 本のみ）。したがって写せるヘッダが存在しない。
- StatsMLlib の既存の FoML 由来ファイルは、いずれも
  `Copyright (c) 2024 Kei Tsukamoto. All rights reserved.` /
  `Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda`
  というヘッダを持つ。

- [ ] 新規 15 ファイルのヘッダを、既存の FoML 由来ファイルに合わせるか、上流の実際の作者に
      合わせるかを PR 00 で決める。
- [ ] 既存ファイルへの追記で著者が増える場合は `Authors` 行に追加する。
- [ ] コミットには必要な `Co-authored-by:` トレーラを入れる。

これは他人の著作物の帰属に関わるため、自分の判断で決めない。
