import Game.Metadata
import Mathlib.Data.Real.EReal

World "Set"
Level 2

Title "Exercise 4.10"

variable (α : Type*)
variable (A B : Set α)

Introduction "Let A, B be sets. Show that A ⊆ B if and only if A ∩ B = A."

Statement : A ⊆ B ↔ A ∩ B = A := by
  Hint "Now your turn! The proof should be analogous to the previous one."
  constructor
  · intro h1
    ext x
    constructor
    · intro h2
      Hint "If in the assumptions we have h: x ∈ A ∩ B, then we know both x ∈ A and x ∈ B.
      Type 'obtain ⟨xa, xb⟩ := h' to obtain xa: x ∈ A and xb: x ∈ B.
      Type '⟨' using '\\<' "
      obtain ⟨xa, xb⟩ := h2
      · exact xa
    · intro h2
      constructor
      · exact h2
      · apply h1
        exact h2
  · intro h1
    intro x
    intro h2
    rw [← h1] at h2
    Hint "If we have h: x ∈ A ∩ B, then h.1 means x ∈ A and h.2 means x ∈ B."
    exact h2.2


/--Tactic 'obtain ⟨H1, H2⟩ := H' (Type '⟨' using '\<') is applied to assumption H: P ∧ Q to obtain two new assumptions H1: P and H2: Q
'obtain H1 | H2 := H is applied to H: P ∨ Q to split into two cases.
--/
TacticDoc obtain
NewTactic obtain

DisabledTheorem eq_zero_of_mul_self_eq_zero
