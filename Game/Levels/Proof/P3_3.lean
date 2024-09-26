import Game.Metadata
import Mathlib.Data.Real.EReal

World "Proof"
Level 3

Title "Exercise 3.3"

variable {A : Type*}

variable {P : A → A → Prop}

Introduction "Let P(x,y) be a predicate over A.
Prove that ∀ x,y ∈ A P(x,y) ↔ P(y,x) if and only if ∀ x,y ∈ A P(x,y) → P(y,x)."


Statement : (∀ (x y : A), P x y → P y x) ↔ (∀ (x y : A), P x y ↔ P y x) := by
  Hint "To prove P ↔ Q, it amounts to prove P → Q and Q → P.

  Type 'constructor' to decompose the goal P ↔ Q into two subgoals P → Q and Q → P."
  constructor
  Hint "Now you have two subgoals: 'Active Goal' and 'Goal 2'.
  You may focus on Goal 2 first by typing 'pick_goal 2'.
  Now your turn!"
  · intro h1
    intro x y
    constructor
    · intro h2
      apply h1
      Hint "If the goal h is exactly in the assumptions, type 'exact h' to solve it.
      Or you can type 'assumption' without specifying the assumption h."
      exact h2
    · intro h3
      apply h1
      exact h3
  · intro h1
    intro x y
    Branch
      have h3 : P x y ↔ P y x := by
        apply h1
      exact h3.1
    Hint "If we already have h: ∀ (x y : A), P x y ↔ P y x,
    then in Lean, (h a b) represents P a b ↔ P b a.
    In Lean, if h is an assumption of the from P ↔ Q, then h.1 represents P → Q
    and h.2 represents Q → P.
    Type 'exact (h x y).1' to solve the goal."
    exact (h1 x y).1


/-- Tactic 'constructor' decompose the goal P ↔ Q into P → Q and Q → P--/
TacticDoc constructor

/--Tactic 'exact h' solves the goal if the goal h is exactly in the assumptions--/
TacticDoc exact

/--Tactic 'assumption' solve the current goal if it is one of the assumptions--/
TacticDoc assumption

/--Tactic 'pick_goal' allows to focus on a specific goal.
Type pick_goal 2 to pick the second goal.--/
TacticDoc pick_goal

NewTactic constructor exact assumption pick_goal

-- /--To prove x=0, it suffice to show x^2=0--/
-- TheoremDoc eq_zero_of_mul_self_eq_zero as "eq_zero_of_mul_self_eq_zero" in "Theorems"

DisabledTheorem eq_zero_of_mul_self_eq_zero
