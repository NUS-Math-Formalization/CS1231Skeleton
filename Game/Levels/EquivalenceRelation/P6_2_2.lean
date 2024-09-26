import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Data.Rat.Defs

World "Equivalence Relations and partial orders"
Level 2

Title "Exercise 6.2"

Introduction "Let R = {(x, y) ∈ ℚ : xy ⩾ 0} be a relation from ℚ to ℚ.
 Decide whether R is symmetric."

-- def R: ℚ → ℚ → Prop := fun (x y : ℚ) => x * y ≥ 0

local infix:50 "R" => fun (x y : ℚ) ↦ x * y ≥ 0

Statement : Symmetric (· R ·) := by
  rw [Symmetric]
  intro x y
  intro h
  Hint "we may use the commutativity of multiplication x*y = y*x here
  Type rw[mul_comm]."
  rw [mul_comm]
  exact h

/--For any a b, a R b implies b R a-/
DefinitionDoc Symmetric as "Symmetric"
NewDefinition Symmetric

/--For any a b ∈ ℚ, a * b = b * a-/
TheoremDoc mul_comm as "mul_comm" in "Theorems"
NewTheorem mul_comm
