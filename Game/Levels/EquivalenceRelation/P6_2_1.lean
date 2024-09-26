import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Data.Rat.Defs

World "Equivalence Relations and partial orders"
Level 1

Title "Exercise 6.2"

Introduction "Let R = {(x, y) ∈ ℚ : xy ⩾ 0} be a relation from ℚ to ℚ.
 Decide whether R is reflexive."

-- def R: ℚ → ℚ → Prop := fun (x y : ℚ) => x * y ≥ 0

local infix:50 "R" => fun (x y : ℚ) ↦ x * y ≥ 0

Statement : Reflexive (· R ·) := by
  Hint "R is reflexive means x R x for any x ∈ Q.
  Type 'rewrite [Reflexive]' or 'dsimp [Reflexive]' (simplify the definition)
  to rewrtie the definition of Reflexive."
  rw [Reflexive]
  apply mul_self_nonneg



/--For any a, a R a-/
DefinitionDoc Reflexive as "Reflexive"
NewDefinition Reflexive

/--For any x ∈ Q, x * x ≥ 0 -/
TheoremDoc mul_self_nonneg as "mul_self_nonneg" in "Theorems"
NewTheorem mul_self_nonneg

/--Tactic 'dsimp' simplify the current goal by unfolding the definitions. -/
TacticDoc dsimp
NewTactic dsimp
