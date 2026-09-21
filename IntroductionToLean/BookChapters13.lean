import Std

/-!
  3章までのサンプルコードを Lean で書き写したもの。
  このファイルは、自然数の基本的な計算と帰納法の使い方を練習するための例題集。
-/

namespace Chapter1

#check Nat
#check Nat.succ
#check Nat.add
#eval 1 + 1
#eval Nat.succ 3

example : 1 + 1 = 2 := by
  rfl

example : 2 + 3 = 5 := by
  decide

end Chapter1

namespace Chapter2

/-- 「2つの引数を足す」定義。 -/
def add (m n : Nat) : Nat :=
  Nat.rec m (fun _ r => Nat.succ r) n

example : add 2 3 = 5 := by
  decide

example : add 0 4 = 4 := by
  rfl

example : add 3 0 = 3 := by
  rfl

end Chapter2

namespace Chapter3

/-- 自然数の加法の定義。Lean の標準 `Nat.add` を使う。 -/
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Nat.add, ih]

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Nat.add, ih]

example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
      simp [Nat.add]
  | succ c ih =>
      simp [Nat.add, ih]

/-- 2 つの自然数の積を再帰的に定義する。 -/
def mul : Nat → Nat → Nat
| m, 0 => 0
| m, n + 1 => mul m n + m

example : mul 3 4 = 12 := by
  decide

example (n : Nat) : mul n 0 = 0 := by
  simp [mul]

example (n : Nat) : mul 0 n = 0 := by
  induction n with
  | zero => simp [mul]
  | succ n ih =>
      simp [mul, ih]

end Chapter3
