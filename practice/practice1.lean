example(P : Prop) (hnp : ¬P) (hp : P) : False := by
  contradiction

example(P Q: Prop)(hnp : ¬P)(hp : P) : Q := by
  exfalso
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

example(P Q:Prop) (h1 : P → Q) (h2 : Q → P) :P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example(P Q:Prop) (hq : Q):(Q → P) ↔ P := by
  constructor

  case mp =>
    intro h
    exact h hq

  case mpr =>
    intro hp hq
    apply hp


example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp =>
    exact h hq
  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
 -- P ↔ Q が仮定にあるので、P の代わりに Q を示せばよい
  rw [h]
 -- 仮定 hq : Q があるので、証明終わり
  exact hq

/-!
『ゼロから始めるLean言語入門』PDF抜粋（本文34-37頁）のコード集。

各コードブロックの直前に、書籍中のコード番号と掲載先を記した。
-/

/-!
コード3.21：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Q が仮定にあるので、P の代わりに Q を示せばよい
  rw [h]

  -- 仮定 hq : Q があるので、証明終わり
  exact hq

/-!
コード3.22：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

/-!
コード3.23：LeanBook/Logic/PropLogic.lean
-/

/-- 同値な命題は等しい -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

/-!
コード3.24：LeanBook/Logic/PropLogic.lean
-/

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

/-!
コード3.25：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-!
コード3.26：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

/-!
コード3.27：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

/-!
コード3.28：LeanBook/Logic/PropLogic.lean
-/

#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

/-!
コード3.29：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

/-!
コード3.30：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

/-!
コード3.31：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

/-!
コード3.32：LeanBook/Logic/PropLogic.lean
-/

example (P Q : Prop) : ( ¬ P ∨ Q) → (P → Q) := by
  intro h
  cases h
  case inl hnp =>
    intro hp
    contradiction
  case inr hq =>
    intro hp
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  case mp =>
    intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq

  case mpr =>
    intro h
    cases h with
    | intro hnp hnq =>
      intro h'
      cases h' with
      | inl hp =>
        apply hnp
        exact hp
      | inr hq =>
        apply hnq
        exact hq
