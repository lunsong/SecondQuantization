import Mathlib.RingTheory.FreeRing
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Star.Free
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Span

namespace Fock

inductive CreAnn (α : Type) : Type
  | cre : α → CreAnn α
  | ann : α → CreAnn α

def cre' {α : Type} (x : α) : FreeAlgebra ℝ (CreAnn α) := FreeAlgebra.ι ℝ (CreAnn.cre x)
def ann' {α : Type} (x : α) : FreeAlgebra ℝ (CreAnn α) := FreeAlgebra.ι ℝ (CreAnn.ann x)

notation (name := anticommute) "[" a "," b "]ₐ" => a * b + b * a

def commutators (α : Type) : Set (FreeAlgebra ℝ (CreAnn α)) := fun x =>
  ( ∃ a b, x = [cre' a, cre' b]ₐ ∨ x = [ann' a, ann' b]ₐ ∨ ( a ≠ b ∧ x = [ann' a, cre' b]ₐ)) ∨
  ( ∃ a, x = [ann' a, cre' a]ₐ - 1)

abbrev Operator (α : Type) : Type :=
  (FreeAlgebra ℝ (CreAnn α)) ⧸ (TwoSidedIdeal.span (commutators α)).asIdeal

def cre {α : Type} (x : α) : Operator α := Ideal.Quotient.mk _ (cre' x)
def ann {α : Type} (x : α) : Operator α := Ideal.Quotient.mk _ (ann' x)

theorem cre_cre {α : Type} (x y : α) : cre x * cre y = -(cre y * cre x) := by
  unfold cre
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  left; rfl

theorem ann_ann {α : Type} (x y : α) : ann x * ann y = -(ann y * ann x) := by
  unfold ann
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  right; left; rfl

theorem ann_cre_ne {α : Type} (x y : α) : x ≠ y → ann x * cre y = -(cre y * ann x) := by
  intro h
  unfold ann cre
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add, ←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  right; right; exact ⟨h, rfl⟩

theorem ann_cre {α : Type} (x : α) :  ann x * cre x = 1 - (cre x * ann x) := by
  unfold ann cre
  apply eq_sub_of_add_eq
  apply eq_of_sub_eq_zero
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    ←(Ideal.Quotient.mk _).map_one,sub_eq_add_neg,←RingHom.map_neg,←RingHom.map_add,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero,←sub_eq_add_neg]
  apply TwoSidedIdeal.subset_span
  unfold commutators
  right
  use x

namespace conjugate

def cre_ann_conj {α : Type} : CreAnn α → CreAnn α
  | CreAnn.cre x => CreAnn.ann x
  | CreAnn.ann x => CreAnn.cre x

lemma cre_ann_conj_involutive {α : Type} : ∀ x : CreAnn α, cre_ann_conj (cre_ann_conj x) = x
  | CreAnn.cre x => by simp only [cre_ann_conj]
  | CreAnn.ann x => by simp only [cre_ann_conj]

--open FreeAlgebra in
--instance creAnnStarRing (α : Type) : StarRing (FreeAlgebra ℝ (CreAnn α)) where
--  star := MulOpposite.unop ∘ (lift ℝ (MulOpposite.op ∘ ι ℝ ∘ cre_ann_conj))
--  star_involutive x := by
--    simp only[Function.comp_apply]
--    let y := lift ℝ (X := CreAnn α) (MulOpposite.op ∘ ι ℝ ∘ cre_ann_conj)
--    refine induction (motive := fun x ↦ (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
--    · simp 
--    · simp [y,cre_ann_conj_involutive]
--    · simp +contextual
--    · simp +contextual
--  star_add a b := by simp
--  star_mul a b := by simp


def cre_ann_conj_alghom {α : Type} : (FreeAlgebra ℝ (CreAnn α)) →ₐ[ℝ] (FreeAlgebra ℝ (CreAnn α)) where
  toFun := FreeAlgebra.lift ℝ (MulOpposite.op ∘ FreeAlgebra.ι ℝ ∘ cre_ann_conj)

instance operatorStarRing (α : Type) : StarRing (Operator α) where
  star := Quotient.lift (Ideal.Quotient.mk _ ∘ star) (by
    intro x y h
    simp
    rw[Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simp [HasEquiv.Equiv]at h


end Fock
