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
  Hint "How to show two relations (sets) are equal?"
  ext a b
  constructor
  · intro h1
    Hint "We may rewrite • by the definition of composition in an assumption h.
    Type 'rewrite [composition] at h' or 'unfold composition at h."
    unfold composition at h1
    Hint "If we have an assumption h: ∃ y, P(y), then we may obtain an object c with P(c).
    Type 'obtain ⟨c, h1⟩ := h' to obtain c and h1: P(c)."
    obtain ⟨c,h2⟩ := h1
    Hint "We may unfold the definition of R now."
    rw [R]
    rw [R] at h2
    rw [R] at h2
    -- Branch
    Hint "If a-c and c-b are both even, then a-b is even as well.
    Since the sum of two even numbers is still even.
    Type 'apply Even_add' to apply this fact."
    Hint
    "Then type 'assumption' to clear the remaining goals (sorry its a bit messy)."
    apply Even_add
    assumption
    -- have h3: Even ((a-c)+(c-b)) := by
    --   apply Even.add
    --   exact h2.1
    --   exact h2.2
    -- rw [sub_add_sub_cancel] at h3
    -- exact h3
  · intro h1
    rw [composition]
    Hint "Which element should we choose?"
    Branch
      use b
      constructor
      · exact h1
      · rw [R]
        Hint "use 'norm_num' or 'simp' here."
        Branch
          norm_num
        simp
    use a
    constructor
    · rw [R]
      Hint "use 'norm_num' or 'simp' here."
      Branch
        norm_num
      simp
    · exact h1

/--Tactic 'simp' simplify the current goal. Can try if you are stuck.-/
TacticDoc simp

/-- R • S means the composition of two relations R and S.
To use • in a tactic, use "composition", e.g, unfold composition. -/
DefinitionDoc composition as "•"
NewDefinition composition

/--If a-b is even and b-c is even, then a-c is also even by adding a-b and b-c.-/
TheoremDoc Even_add as "Even_add" in "Theorems"
NewTheorem Even_add

-- /--Tactic 'obtain ⟨H1, H2⟩ := H' is applied to assumption H: P ∧ Q to obtain two new assumptions H1: P and H2: Q
-- 'obtain H1 | H2 := H is applied to H: P ∨ Q to split into two cases.
-- 'obtain ⟨c,h1⟩ := H is applied to H: ∃ y P(y).--/
-- TacticDoc obtain
NewTactic simp

-- OnlyTheorem Even_add
