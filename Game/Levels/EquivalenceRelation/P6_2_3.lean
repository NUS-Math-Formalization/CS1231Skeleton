import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

World "Equivalence Relations and partial orders"
Level 3

Title "Exercise 6.2"

Introduction "Let R = {(x, y) ∈ ℚ : xy ⩾ 0} be a relation from ℚ to ℚ.
 Decide whether R is antisymmetric."

-- def R: ℚ → ℚ → Prop := fun (x y : ℚ) => x * y ≥ 0

local infix:50 "R" => fun (x y : ℚ) ↦ x * y ≥ 0

Statement : ¬ AntiSymmetric (· R ·) := by
  rw [AntiSymmetric]
  Hint "We may directly simplify our goal by pushing the negation inside
  applying De Morgan's rule. Type 'push_neg' to simplify the goal."
  push_neg
  Hint "What is your counterexample?"
  use 1, 2
  norm_num


/--For any a b, a R b and b R a implies a = b-/
DefinitionDoc AntiSymmetric as "AntiSymmetric"
NewDefinition AntiSymmetric

/--Tactic "push_neg" pushes the outside ¬ to inside using De Morgan's rule.-/
TacticDoc push_neg

/-- Tactic "norm_num" solve the problem of verifying computational facts,
 e.g, 1+1=2.-/
TacticDoc norm_num
NewTactic norm_num push_neg
