import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Data.Rat.Defs

World "Equivalence Relations and partial orders"
Level 5

Title "Exercise 6.2"

Introduction "Let S be a relation on R^2 by setting, for all (x1, y1), (x2, y2) ∈ R2,
(x1, y1) S (x2, y2) ⇔ x1 ⩽ x2 and y1 ⩽ y2.
Decide whether R is reflexive."

local infix:50 "S" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

Statement : Reflexive (· S ·) := by
  simp [Reflexive]
