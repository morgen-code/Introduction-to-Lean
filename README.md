# ペアノの公理系から始める Lean 入門

このリポジトリは、Lean で自然数・整数の基本定理を証明していくための入門資料です。

最初にペアノの公理系を思い出し、次の順で進めます。

1. `zero` と `succ` による自然数の定義
2. 足し算の再帰的定義
3. `add_zero` と `add_succ`
4. 結合法則
5. 交換法則
6. 整数の加法へ接続

## 参考書籍

- [ゼロから始めるLean言語入門](https://www.lambdanote.com/products/leanbook)
- [An introduction to mathematical proof](https://adam.math.hhu.de/#/g/leanprover-community/nng4)

## 主要ファイル

- [IntroductionToLean/Basic.lean](IntroductionToLean/Basic.lean)
- [Main.lean](Main.lean)

## 例

```lean
import IntroductionToLean.Basic

open Peano

example : Peano.PeanoNat.add (Peano.PeanoNat.succ Peano.PeanoNat.zero) Peano.PeanoNat.zero
    = Peano.PeanoNat.succ Peano.PeanoNat.zero := by
  simp [Peano.PeanoNat.add]
```

## 学習の流れ

- まずは自然数の定義を理解する
- 再帰的な定義に慣れる
- 帰納法で命題を証明する
- 最後に整数の加法を見て、可換性を確認する

この順番を守ると、Lean で数学の証明を書く感覚が自然に身につきます。
