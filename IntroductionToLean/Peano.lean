inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, zero    => n
  | n, succ m  => succ (add n m)

instance : Add MyNat := ⟨add⟩

def one : MyNat := succ zero
def two : MyNat := succ (succ zero)

theorem one_add_one : one + one = two := by
  show add one one = two
  unfold add one two
  rfl

end MyNat
