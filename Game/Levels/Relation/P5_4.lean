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
  Hint "We may rewrite R⁻¹ by the definition of inverse using 'rewrite [inverse]'."
  Hint "We may also unfold the definition of R using 'rewrite [R]' or 'unfold R'.
  To unfold the definition of R in an assumption h,
  Type 'rewrite [R] at h' or 'unfold R at h."
  Branch
    rw [Rel.inv_def]
    unfold R
    Hint "a-b is even if and only if b-a is even.
    Type 'Even_negation_iff' to apply this."
    apply Even_negation_iff
  constructor
  · intro h1
    Hint "We may rewrite R⁻¹ by the definition of inverse using rw [inverse]."
    Hint "We may also unfold the definition of R using rw [R] or unfold [R].
    To unfold the definition of R in an assumption h,
    we may use the tactic 'rewrite [R] at h' or 'unfold R at h."
    rw [Rel.inv_def]
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
    rw [Rel.inv_def] at h1
    rw [R] at h1
    rw [R]
    apply Even_negation
    exact h1


/--Tactic 'simp' simplify the current goal.-/
TacticDoc simp


/--Tactic 'unfold R' unfolds a definition R. It is the same as rw [R].
 'unfold R at h' unfolds the definition R in the assumption h -/
TacticDoc unfold

/--Tactic 'rewrite [h]' or 'rewrite [← h]' rewrite the current goal with assumption h,
where h is usually an equivalence, equation or a definition.
'rewrite [h] at h1' rewrites the assumption h1 with h -/
TacticDoc rewrite

NewTactic simp unfold rewrite

/--If a-b is even, then so do b-a.-/
TheoremDoc Even_negation as "even_negation" in "Theorems"

/--a-b is even if and only if b-a is even.-/
TheoremDoc Even_negation_iff as "even_negation_iff" in "Theorems"


/--'inv_def' states the definition of the inverse of relations. R.inv a b if and only if R b a.-/
TheoremDoc Rel.inv_def as "inverse" in "Theorems"
NewTheorem Even_negation Even_negation_iff Rel.inv_def

/--For any a,b ∈ ℤ, a R b if and only if a-b is even -/
DefinitionDoc R as "R"
NewDefinition R

OnlyTheorems Even_negation Even_negation_iff Rel.inv_def
