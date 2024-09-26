import Game.Metadata
import Mathlib.Data.Real.EReal

World "Proof"
Level 1

Title "Exercise 3.2"

Introduction "Prove 'there is a real number x such that x^2 + 9 = 6x'."

Statement : ∃ x : ℝ, x ^ 2 + 9 = 6 * x := by
  Hint "We prove theorems here using Tactics. The first tactic is 'use'."
  Hint "To show there exists some object x, we only need to provide a witness.
   That is, some a ∈ ℝ such that a^2 + 9 = 6 * a.
   Type 'use a' in the textbox to give the witness, where a ∈ ℝ is the solution to the equation."
  use 3
  Hint "Now you need to prove that 3^2 + 9 = 6 * 3.
  Fortunately, this can be done by some automatic tactics.

  Type 'linarith' or 'norm_num' to verify the equation."
  Branch
    linarith
  norm_num


Conclusion "'use' is a tactic.
 If you ever want information about the tactic,
 you can click on 'use' in the list of tactics on the right."


/--Tactic 'linarith' verifies linear equations automatically.--/
TacticDoc linarith

/--Tactic 'norm_num' verifies arithmetic equations automatically.-/
TacticDoc norm_num

/--Tactic 'use a' proves goal ∃x ∈ A... if a is the witness.--/
TacticDoc use
NewTactic linarith use norm_num
