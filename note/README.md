# note

このディレクトリは移植作業用で、**`main` にはマージしない**（`plan.md` の付録 C-2）。
`reflect/plan` ブランチに置き、issue からリンクする。

| ファイル | 内容 |
|---|---|
| [`plan.en.md`](plan.en.md) | 作業計画（英語）。リポジトリの他の文書が英語なので、issue や PR からはこちらをリンクする。 |
| [`plan.md`](plan.md) | 同じ内容の日本語版。 |
| [`upstream/plan.md`](upstream/plan.md) | 上流 `auto-res/lean-rademacher` ブランチ `ss`（HEAD `d50ea5c`）の `note/plan.md` そのまま。参照用。 |
| [`upstream/summary.md`](upstream/summary.md) | 同じく上流の `note/summary.md` そのまま。上流実装の全体像と公開 API の一覧。 |

読む順序は **付録 C（PR の順序）→ 該当する本文の節**。付録 C-3 の各 PR 行が本文の節を指している。

`upstream/` の 2 ファイルは `FoML/...` という上流のモジュール名で書かれている。
StatsMLlib のモジュールとの対応は `plan.md` / `plan.en.md` の §0.3 にある。編集しないこと。

`plan.en.md` と `plan.md` は節番号・小見出し・チェックボックス・表がすべて 1 対 1 に対応している。
**片方だけ更新しない。** 二重管理が負担になったら、英語版を正本にして日本語版を落とす。
