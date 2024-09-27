import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Logic.Relation
import Mathlib.Data.Rel
import Game.Levels.Relation.RelationLemmas

World "Relation"
Level 1

Title "Exercise 5.4 (1)"


Introduction "Let R be a relation from ℤ to ℤ such that R a b if and only if a-b is even.
Prove that R = R⁻¹."

-- def R : Rel ℤ ℤ := fun a b => Even (a - b)


Statement : R = R⁻¹ := by
  Hint "Relations are sets, so to prove R = R⁻¹ as set equality,
  we can use tactic 'ext a b'."
  ext a b
  Hint "We may rewrite R⁻¹ by the definition of inverse using 'rewrite [Inverse]'."
  Hint "We may also unfold the definition of R using 'rewrite [R]' or 'unfold R'.
  To unfold the definition of R in an assumption h,
  Type 'rewrite [R] at h' or 'unfold R at h."
  Branch
    rw [Inverse]
    unfold R
    Hint "a-b is even if and only if b-a is even.
    Type 'apply Even_negation_iff' to apply this."
    apply Even_negation_iff
  constructor
  · intro h1
    Hint "We may rewrite R⁻¹ by the definition of inverse using rw [Inverse]."
    Hint "We may also unfold the definition of R using rw [R] or unfold [R].
    To unfold the definition of R in an assumption h,
    we may use the tactic 'rewrite [R] at h' or 'unfold R at h."
    rw [Inverse]
    unfold R at h1
    unfold R
    Hint "To prove b-a is even, it suffices to prove a-b is even.
    Type 'apply Even_negation' to apply this."
    apply Even_negation
    exact h1
  · intro h1
    -- Hint "We may rewrite R.inv by its definition using rewrite [inverse]."
    -- Hint "We may also unfold the definition of R using rewrite [R] or unfold [R].
    -- To unfold the definition of R in an assumption h,
    -- we may use the tactic 'rewrite [R] at h' or 'unfold R at h."
    rw [Inverse] at h1
    rw [R] at h1
    rw [R]
    apply Even_negation
    exact h1


/--Tactic 'simp' simplify the current goal. Can try if you are stuck.-/
TacticDoc simp


/--Tactic 'unfold A' unfolds a definition A. It is the same as rewrite [A].
 'unfold A at h' unfolds the definition A in the assumption h
Here A could be Inverse, composition, or the definition of R in the question -/
TacticDoc unfold

/--Tactic 'rewrite [h]' or 'rewrite [← h]' rewrite the current goal with assumption h,
where h is usually an equivalence, equation or a definition.
'rewrite [h] at h1' rewrites the assumption h1 with h
Here h could be a equivalence, equation or some definition.-/
TacticDoc rewrite

NewTactic simp unfold rewrite

/--If a-b is even, then so do b-a.-/
TheoremDoc Even_negation as "Even_negation" in "Theorems"

/--a-b is even if and only if b-a is even.-/
TheoremDoc Even_negation_iff as "Even_negation_iff" in "Theorems"


/--'Inverse' states the definition of the inverse of relations. R⁻¹ a b if and only if R b a.-/
TheoremDoc Inverse as "Inverse" in "Theorems"
NewTheorem Even_negation Even_negation_iff Inverse

/--For any a,b ∈ ℤ, a R b if and only if a-b is even -/
DefinitionDoc R as "R"

/--b R⁻¹ a if and only if a R b-/
DefinitionDoc Rel.inv as "⁻¹"
NewDefinition R Rel.inv

OnlyTheorem Even_negation Even_negation_iff Inverse
