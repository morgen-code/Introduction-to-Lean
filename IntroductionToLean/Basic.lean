import Std

/-!
# ペアノの公理系から始める Lean 入門

このファイルでは、自然数を `zero` と `succ` で定義し、
足し算の基本定理を帰納法で証明していく。
-/

namespace Peano

/-- ペアノの自然数。 -/
inductive PeanoNat
| zero
| succ (n : PeanoNat)

namespace PeanoNat

/-- 自然数の加法。 `n + 0 = n`, `n + (m+1) = (n+m)+1` -/
def add : PeanoNat → PeanoNat → PeanoNat
| a, zero => a
| a, succ b => succ (add a b)

/-- 零加法: `a + 0 = a` -/
theorem add_zero : ∀ a : PeanoNat, add a zero = a
| zero => rfl
| succ a => by
    simp [add]

/-- 右側の零加法: `0 + a = a` -/
theorem add_zero_right : ∀ a : PeanoNat, add zero a = a
| zero => rfl
| succ a => by
    simp [add, add_zero_right a]

/-- 後者への加法: `a + (b+1) = (a+b) + 1` -/
theorem add_succ (a b : PeanoNat) : add a (succ b) = succ (add a b) := by
  simp [add]

/-- 左側の後者への加法: `(a+1) + b = a + b + 1` -/
theorem succ_add : ∀ a b : PeanoNat, add (succ a) b = succ (add a b)
| a, zero => by
    simp [add]
| a, succ b => by
    simp [add, succ_add a b]

/-- 結合法則: `(a + b) + c = a + (b + c)` -/
theorem add_assoc : ∀ a b c : PeanoNat, add (add a b) c = add a (add b c)
| a, b, zero => by
    simp [add]
| a, b, succ c => by
    simp [add, add_assoc a b c]

/-- 交換法則: `a + b = b + a` -/
theorem add_comm : ∀ a b : PeanoNat, add a b = add b a
| a, zero => by
    simp [add, add_zero_right]
| a, succ b => by
    rw [add_succ, succ_add, add_comm a b]

end PeanoNat

end Peano

namespace IntegerIntro

/-- 整数の加法の交換法則。 -/
example (a b : Int) : a + b = b + a := by
  simpa using Int.add_comm a b

/-- 整数の加法の結合法則。 -/
example (a b c : Int) : (a + b) + c = a + (b + c) := by
  simpa using Int.add_assoc a b c

end IntegerIntro
