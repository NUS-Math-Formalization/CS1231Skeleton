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
      Type '⟨' using '\\ <' "
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
    Hint "Here we need to replace the assumption h1: x ∈ A
    by x ∈ A ∩ B using the assumption h2: A ∩ B = A.
    Type 'rewrite [h2] at h1' to rewrite the goal."
    rw [← h1] at h2
    Hint "If we have h: x ∈ A ∩ B, then h.1 means x ∈ A and h.2 means x ∈ B."
    exact h2.2


-- /--asdfdfasdf.
-- --/
-- TacticDoc obtain
-- NewTactic obtain

DisabledTheorem eq_zero_of_mul_self_eq_zero
