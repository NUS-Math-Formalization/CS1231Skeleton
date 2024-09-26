import Game.Metadata
import Mathlib.Data.Real.EReal

World "Proof"
Level 2

Title "Exercise 3.2 continued"

Introduction "This is what he proved.
 Compare the difference of the two statements and their proofs."

-- TacticDoc linarith



Statement : ∀ x : ℝ, (x ^ 2 + 9 = 6 * x → x - 3 = 0) := by
  Hint "To prove 'For any x ∈ ℝ ...', one start with picking an arbitrary a ∈ ℝ.

  Type 'intro a' to pick such a.
  (The name 'a' is arbitrary and can be replaced by any name)"
  intro a
  Hint "To prove P → Q, it amounts to take P as an assumption and prove Q.
  Type 'intro h1' to let P be an assumption h1 and our goal becomes Q."
  intro h1
  Hint "To prove 'x - 3 = 0', it suffice to show (x-3)^2=0.
  The theorem 'eq_zero_of_mul_self_eq_zero' can be used to prove this.
  Type 'apply eq_zero_of_mul_self_eq_zero' to apply this theorem."
  apply eq_zero_of_mul_self_eq_zero
  Hint "'linarith' or 'norm_num will check (a - 3)*(a - 3) = a^2 - 6a + 9 holds."
  Branch
    norm_num
  linarith


/--'intro' introduce an element (for '∀x...') or an assumption (for 'P → Q').--/
TacticDoc intro

/--'apply T' applies a theorem T to the goal.--/
TacticDoc apply

-- /--exact h solves the goal if the goal h is exactly in the assumptions--/
-- TacticDoc exact
NewTactic intro apply

/--To prove x=0, it suffice to show x^2=0--/
TheoremDoc eq_zero_of_mul_self_eq_zero as "eq_zero_of_mul_self_eq_zero" in "Theorems"

NewTheorem eq_zero_of_mul_self_eq_zero
