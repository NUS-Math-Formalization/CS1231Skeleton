import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Logic.Relation
import Mathlib.Data.Rel
import Game.Levels.Relation.RelationLemmas

World "Relation"
Level 2

Title "Exercise 5.4 (2)"
-- /-- Composition of relation; note that it follows the `CategoryTheory/` order of arguments. -/


-- def composition  (r : Rel α β) (s : Rel β γ): Rel α γ := fun x z => ∃ y, r x y ∧ s y z

-- -- Porting note: the original `∘` syntax can't be overloaded here, lean considers it ambiguous.
-- -- TODO: Change this syntax to something nicer?
-- /-- Local syntax for composition of relations. -/
-- notation: 90 a "•" b => composition a b

Introduction "Let R be a relation from ℤ to ℤ such that R a b if and only if a-b is even.
Prove that R = R • R."

-- def R : Rel ℤ ℤ := fun a b => Even (a - b)



Statement : (R • R) = R := by
  ext a b
  constructor
  · intro h1
    Hint "We may rewrite • by the definition of composition in an assumption h.
    Type 'rw [composition] at h' or 'unfold composition at h."
    unfold composition at h1
    Hint "If we have an assumption h: ∃ y, P(y), then we may obtain an object c with P(c).
    Type 'obtain ⟨c, h1⟩ := h' to obtain c and h2: P(c)."
    obtain ⟨c,h2⟩ := h1
    rw [R]
    rw [R] at h2
    rw [R] at h2
    -- Branch
    Hint "If a-c and c-b are both even, then a-b is even as well.
    Since the sum of two even numbers is still even.
    Type 'apply Even_add' to apply this fact."
    apply Even_add
    Hint "Type assumption to clear the remaining goals."
    assumption
    -- have h3: Even ((a-c)+(c-b)) := by
    --   apply Even.add
    --   exact h2.1
    --   exact h2.2
    -- rw [sub_add_sub_cancel] at h3
    -- exact h3
  · intro h1
    rw [composition]
    rw [R] at h1
    use a
    constructor
    · rw [R]
      simp
    · rw [R]
      exact h1

/-- R • S means the composition of two relations R and S.
To use • in a tactic, use "composition", e.g, unfold composition. -/
DefinitionDoc composition as "•"
NewDefinition composition

/--If a-b is even and b-c is even, then a-c is also even by adding a-b and b-c.-/
TheoremDoc Even_add as "Even_add" in "Theorems"
NewTheorem Even_add

/--Tactic 'obtain ⟨H1, H2⟩ := H' is applied to assumption H: P ∧ Q to obtain two new assumptions H1: P and H2: Q
'obtain H1 | H2 := H is applied to H: P ∨ Q to split into two cases.
'obtain ⟨c,h1⟩ := H is applied to H: ∃ y P(y).--/
TacticDoc obtain
NewTactic obtain
