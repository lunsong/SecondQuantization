import Mathlib.Tactic

def antiComm {R : Type} [Semiring R] (x y : R) : R := x * y + y * x

class Fermion (α : Type) [DecidableEq α] (R : Type) [CommRing R] [StarRing R]
  (operator : Type) [Semiring operator] [Module R operator] [StarRing operator] where
  cre : α → operator
  ann : α → operator
  cre_cre : ∀ x y, antiComm (cre x) (cre y) = 0
  ann_ann : ∀ x y, antiComm (ann x) (ann y) = 0
  cre_ann : ∀ x y, antiComm (cre x) (ann y) = if x = y then 1 else 0
  star_cre : ∀ x, star (cre x) = ann x
  vacExpect : operator →ₗ[R] R
  vacExpect_star : ∀ A, vacExpect (star A) = star (vacExpect A)
  vacExpect_cre_mul : ∀ x, ∀ A, vacExpect (cre x * A) = 0
  vacExpect_one : vacExpect 1 = 1

variable (α : Type) [DecidableEq α] (R : Type) [CommRing R] [StarRing R] (operator : Type)
  [Semiring operator] [Module R operator] [StarRing operator] [Fermion α R operator]

theorem Fermion.vacExpect_mul_star (A : operator) :
    IsSquare (vacExpect (R := R) (operator := operator) α (A * star A)) := sorry

open Fermion in
example (α : Type) [DecidableEq α] (R : Type) [CommRing R] [StarRing R]
  (operator : Type) [Semiring operator] [Module R operator] [StarRing operator]
  [Fermion α R operator] :
    ∀ a : α, vacExpect α (ann R a * cre R a : operator) = (1 : R) := by
  intro a
  have := cre_ann (α := α) (R := R) (operator := operator) a a
  simp only [antiComm, ↓reduceIte] at this
  apply congrArg (vacExpect (R := R) α) at this
  simpa only [map_add, vacExpect_one, vacExpect_cre_mul, zero_add] using this

