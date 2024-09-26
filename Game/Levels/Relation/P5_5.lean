import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Logic.Relation
import Mathlib.Data.Rel
import Game.Levels.Relation.RelationLemmas

World "Relation"
Level 3



variable (A B C D : Type*)
variable (R : Rel A B)
variable (S : Rel B C)
variable (T : Rel C D)

-- local infixr:90 " • " => composition

Introduction "Let A B C D be sets, R is a relation from A to B,
S is a relation from B to C, and T is a relation from C to D.
Prove that T • (S• R) = (T • S) • R."

Statement : (T • (S • R))  = ((T • S) • R) := by
  ext a d
  Branch
    unfold composition
    Hint "Actually the two expressions are logically equal,
     type 'tauto' to prove it."
    tauto
  constructor
  · intro h1
    rw [composition] at h1
    obtain ⟨c,h2⟩ := h1
    obtain ⟨h3,h4⟩ := h2
    -- obtain ⟨h3, h4⟩ := h2
    rw [composition] at h3
    obtain ⟨b, h5⟩ := h3
    rw [composition]
    use b
    constructor
    · exact h5.1
    · rw [composition]
      use c
      constructor
      · exact h5.2
      · exact h4
  · intro h1
    rw [composition] at h1
    obtain ⟨b,h2⟩ := h1
    obtain ⟨h3, h4⟩ := h2
    rw [composition] at h4
    obtain ⟨c,h5⟩ := h4
    rw [composition]
    use c
    constructor
    · rw [composition]
      use b
      constructor
      · exact h3
      · exact h5.1
    · exact h5.2



/--Tactic "tauto" deal with purely logical deduction.-/
TacticDoc tauto
NewTactic tauto

DisabledTheorem Even_negation_iff Even_negation Even_add eq_zero_of_mul_self_eq_zero
