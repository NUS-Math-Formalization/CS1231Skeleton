import Game.Metadata
import Mathlib.Data.Real.EReal

World "Set"
Level 1

Title "Exercise 4.6"

variable (α : Type*)
variable (A B : Set α)

Introduction "Let A, B be sets, prove that A ⊆ B if and only if A ∪ B = B."

Statement : A ⊆ B ↔ A ∪ B = B := by
  Hint "In case you jump tp Chapter 4, click Tactic 'constructor' on the right."
  constructor
  · intro h1
    Hint "To prove A ∪ B = B, it suffices to prove for all x, x ∈ A ∪ B ↔ x ∈ B.
    Type 'ext x' or 'ext' to introduce an element x and prove the equivalence."
    ext x
    Hint "How do you prove something with '↔' ?"
    constructor
    · intro h2
      Hint "From the assumption 'h: x ∈ A ∪ B', we may split into two cases with assumption 'x ∈ A' or 'x ∈ B'.
      Type 'obtain xa | xb := h' to split into two cases with 'xa: x ∈ A' or 'xb: x ∈ B'."
      obtain xa | xb := h2
      · apply h1
        exact xa
      · exact xb
    · intro h2
      Hint "To prove x ∈ A ∪ B, it suffice to prove x ∈ A ∨ x ∈ B.
      Type 'left' to prove x ∈ A or 'right' to prove x ∈ B."
      right
      exact h2
  · intro h1
    intro x
    intro h2
    Hint "Since we already have assumption h: A ∪ B = B, we may rewrite the goal x ∈ B by x ∈ A ∪ B.
    Type 'rewrite [← h]' (or whatever name for A ∪ B = B) to rewrite the goal.
    Here ← means we are rewriting from right to left in the equation A ∪ B = B."
    rw [← h1]
    left
    exact h2


/--Tactic 'obtain H1 | H2 := H' split the assumption H: P ∨ Q into two cases
 with assumption H1: P or H2: Q respectively--/
TacticDoc obtain

/--Tactic 'ext x' reduce the goal A = B to x ∈ A ↔ x ∈ B
or simply 'ext'
 -/
TacticDoc ext

/--Tactic 'left' reduce the goal P ∨ Q to P.-/
TacticDoc left

/--Tactic 'right' reduce the goal P ∨ Q to Q.-/
TacticDoc right

/--Tactic 'rewrite [h]' or 'rewrite [← h]' rewrite the current goal with assumption h,
where h is usually an equivalence or an equation-/
TacticDoc rewrite

/--'rw' is the same as 'rewrite-/
TacticDoc rw

NewTactic ext left right rewrite rw


DisabledTheorem eq_zero_of_mul_self_eq_zero
