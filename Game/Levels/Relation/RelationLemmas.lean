import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Algebra.Parity
import Mathlib.Logic.Relation
import Mathlib.Data.Rel


def composition (s : Rel β γ) (r : Rel α β) : Rel α γ := fun x z => ∃ y, r x y ∧ s y z

-- Porting note: the original `∘` syntax can't be overloaded here, lean considers it ambiguous.
-- TODO: Change this syntax to something nicer?
/-- Local syntax for composition of relations. -/
-- local infixr:90 " • " => composition
notation: 90 a "•" b => composition a b

set_option quotPrecheck false

notation:max R"⁻¹" => Rel.inv R


def R : Rel ℤ ℤ := fun a b => Even (a - b)
lemma Even_negation_iff (a b: ℤ): Even (a-b) ↔ Even (b-a) := by
    constructor
    · intro h
      apply even_neg.1
      simp
      exact h
    · intro h
      apply even_neg.1
      simp
      exact h

lemma Even_negation (a b: ℤ): Even (a-b) → Even (b-a) := by
    intro h
    apply even_neg.1
    simp
    exact h

lemma Even_add (a b c: ℤ) (h: Even (a-c) ∧ Even (c-b)) : Even (a-b) := by
  rw [← sub_add_sub_cancel a c b]
  apply Even.add
  exact h.1
  exact h.2
