import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

World "Equivalence Relations and partial orders"
Level 4

Title "Exercise 6.2"

Introduction "Let R = {(x, y) ∈ ℚ : xy ⩾ 0} be a relation from ℚ to ℚ.
 Decide whether R is transitive."

-- def R: ℚ → ℚ → Prop := fun (x y : ℚ) => x * y ≥ 0

local infix:50 "R" => fun (x y : ℚ) ↦ x * y ≥ 0

Statement : ¬ Transitive (· R ·) := by
  simp [Transitive]
  push_neg
  use 1, 0, -1
  norm_num



/--For any a b c, a R b and b R c implies a R c.-/
DefinitionDoc Transitive as "Transitive"
NewDefinition Transitive
