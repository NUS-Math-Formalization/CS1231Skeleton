import Game.Metadata
import Mathlib.Data.Real.EReal
import Mathlib.Logic.Relation
import Mathlib.Data.Rel
import Game.Levels.Relation.RelationLemmas

World "Relation"
Level 4

Title "Exercise 5.9"


Introduction "Let A, B be sets, R be a relation from A to B.
Prove that R = (R⁻¹)⁻¹."



variable (A B : Type*)

variable (R : Rel A B)
set_option quotPrecheck false
-- notation:max "R⁻¹" => Rel.inv R

Statement : R = (R⁻¹)⁻¹ := by
  ext a b
  rw [Rel.inv_def]
  rw [Rel.inv_def]
