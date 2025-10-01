import Mathlib.RingTheory.FreeRing
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Star.Free
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace Fock

inductive CreAnn (α : Type) : Type
  | cre : α → CreAnn α
  | ann : α → CreAnn α

abbrev cre' {α : Type} (x : α) : FreeAlgebra ℝ (CreAnn α) := FreeAlgebra.ι ℝ (CreAnn.cre x)
abbrev ann' {α : Type} (x : α) : FreeAlgebra ℝ (CreAnn α) := FreeAlgebra.ι ℝ (CreAnn.ann x)

notation (name := anticommute) "[" a "," b "]ₐ" => a * b + b * a

abbrev commutators (α : Type) : Set (FreeAlgebra ℝ (CreAnn α)) := fun x =>
  ( ∃ a b, x = [cre' a, cre' b]ₐ ∨ x = [ann' a, ann' b]ₐ ∨ ( a ≠ b ∧ x = [ann' a, cre' b]ₐ)) ∨
  ( ∃ a, x = [ann' a, cre' a]ₐ - 1)

abbrev Operator (α : Type) : Type :=
  (FreeAlgebra ℝ (CreAnn α)) ⧸ (TwoSidedIdeal.span (commutators α)).asIdeal

abbrev cre {α : Type} (x : α) : Operator α := Ideal.Quotient.mk _ (cre' x)
abbrev ann {α : Type} (x : α) : Operator α := Ideal.Quotient.mk _ (ann' x)

theorem cre_cre {α : Type} (x y : α) : cre x * cre y = -(cre y * cre x) := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  left; rfl

theorem ann_ann {α : Type} (x y : α) : ann x * ann y = -(ann y * ann x) := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  right; left; rfl

theorem ann_cre_ne {α : Type} (x y : α) : x ≠ y → ann x * cre y = -(cre y * ann x) := by
  intro h
  apply eq_neg_iff_add_eq_zero.mpr
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add, ←(Ideal.Quotient.mk _).map_zero,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero]
  apply TwoSidedIdeal.subset_span
  left
  use x,y
  right; right; exact ⟨h, rfl⟩

theorem ann_cre {α : Type} (x : α) :  ann x * cre x = 1 - (cre x * ann x) := by
  apply eq_sub_of_add_eq
  apply eq_of_sub_eq_zero
  rw[←RingHom.map_mul,←RingHom.map_mul,←RingHom.map_add,←(Ideal.Quotient.mk _).map_zero,
    ←(Ideal.Quotient.mk _).map_one,sub_eq_add_neg,←RingHom.map_neg,←RingHom.map_add,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero,←sub_eq_add_neg]
  apply TwoSidedIdeal.subset_span
  right
  use x

namespace injectivity

noncomputable def to_polynomial {α : Type} : (FreeAlgebra ℝ (CreAnn α)) →ₐ[ℝ] Polynomial ℝ :=
  FreeAlgebra.lift ℝ fun _ ↦ Polynomial.X

end injectivity

theorem zero_ne_one {α : Type} : (0 : Operator α) ≠ 1 := by
  rw[Ideal.Quotient.zero_ne_one_iff,Ideal.ne_top_iff_one,TwoSidedIdeal.mem_asIdeal]
  suffices h : ∀ x ∈ TwoSidedIdeal.span (commutators α), x ≠ 1 from fun hc ↦ h 1 hc rfl
  intro x
  refine TwoSidedIdeal.span_induction ?_ ?_ ?_ ?_ ?_ ?_
  · intro x h
    rcases h with ⟨a, b, h | h | h⟩ | ⟨a, h⟩
    · rw[h,cre',cre']
      intro hc
      replace hc := congrArg FreeAlgebra.algebraMapInv hc
      simp [FreeAlgebra.algebraMapInv] at hc
    · rw[h,ann',ann']
      intro hc
      replace hc := congrArg FreeAlgebra.algebraMapInv hc
      simp [FreeAlgebra.algebraMapInv] at hc
    . rw[h.2,ann',cre']
      intro hc
      replace hc := congrArg FreeAlgebra.algebraMapInv hc
      simp [FreeAlgebra.algebraMapInv] at hc
    · rw[h,ann',cre']
      intro hc
      replace hc := congrArg FreeAlgebra.algebraMapInv hc
      simp [FreeAlgebra.algebraMapInv] at hc
      rw[←add_eq_zero_iff_neg_eq] at hc
      simp at hc
  · simp
  · intro x y hx hy h₁ h₂


theorem cre_inj {α : Type} : Function.Injective (@cre α) := by
  intro x y h
  by_contra! hc
  have := (ann_cre _) ▸ h ▸ (ann_cre_ne _ _ hc)
  rw[sub_eq_iff_eq_add,neg_add_cancel] at this
  replace this := this.symm
  exact zero_ne_one this


/-

theorem zero_ne_one {α : Type} : (0 : Operator α) ≠ 1 := by
-/


namespace conjugation

def conj₀ {α : Type} : CreAnn α → CreAnn α
  | CreAnn.cre x => CreAnn.ann x
  | CreAnn.ann x => CreAnn.cre x

lemma conj₀_involutive {α : Type} : ∀ x : CreAnn α, conj₀ (conj₀ x) = x
  | CreAnn.cre x => by simp only [conj₀]
  | CreAnn.ann x => by simp only [conj₀]

def conj₁ {α : Type} : (FreeAlgebra ℝ (CreAnn α)) →ₐ[ℝ] (FreeAlgebra ℝ (CreAnn α))ᵐᵒᵖ :=
  FreeAlgebra.lift ℝ (MulOpposite.op ∘ FreeAlgebra.ι ℝ ∘ conj₀)

def conj₂ {α : Type} : (FreeAlgebra ℝ (CreAnn α)) → Operator α :=
  Ideal.Quotient.mk _ ∘ MulOpposite.unop ∘ conj₁

def conj {α : Type} : Operator α → Operator α :=
  Quotient.lift conj₂ (by
    intro a b h
    rw[←Quotient.eq_iff_equiv] at h
    have : (Ideal.Quotient.mk _ a : Operator α) = Ideal.Quotient.mk _ b := by
      simpa [←Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk]
    simp only [conj₂,Function.comp_apply,Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this ⊢
    rw [←MulOpposite.unop_sub, ←map_sub]
    rw [TwoSidedIdeal.mem_asIdeal] at this
    generalize a - b = x at this ⊢
    refine TwoSidedIdeal.span_induction ?_ ?_ ?_ ?_ ?_ ?_ this
    · intro x h
      rw [TwoSidedIdeal.mem_asIdeal]
      apply TwoSidedIdeal.subset_span
      rcases h with h | h
      · rcases h with ⟨a, b, h | h | h⟩
        · simp[h,conj₁,conj₀]; left; use b,a; right; left; rfl
        · simp[h,conj₁,conj₀]; left; use b,a; left; rfl
        · simp[h.2,conj₁,conj₀]; left; use b,a; right; right; exact ⟨h.1.symm, rfl⟩
      obtain ⟨a, h⟩ := h
      simp[h, conj₁, conj₀]; right; use a
    · simp only [map_zero, MulOpposite.unop_zero, zero_mem]
    · intro x y _ _ h₁ h₂
      rw[map_add,MulOpposite.unop_add]
      exact Ideal.add_mem _ h₁ h₂
    · intros
      rwa[map_neg,MulOpposite.unop_neg,Ideal.neg_mem_iff]
    · intro x y _ h
      rw[map_mul,MulOpposite.unop_mul]
      exact TwoSidedIdeal.mul_mem_right _ _ _ h
    · intro x y _ h
      rw[map_mul,MulOpposite.unop_mul]
      exact TwoSidedIdeal.mul_mem_left _ _ _ h
  )

theorem mk_eq_mk {α : Type} (a : FreeAlgebra ℝ (CreAnn α)) :
    (Ideal.Quotient.mk _ a: Operator α) = ⟦a⟧ := rfl

set_option synthInstance.maxHeartbeats 30000 in 
-- This is needed otherwise lean will fail to synthesize AddHomClass for Ideal.Quotient.mk
instance operatorStarRing (α : Type) : StarRing (Operator α) where
  star := conj
  star_involutive x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro x
    rw[Submodule.Quotient.mk]
    simp[conj,conj₂,←Ideal.Quotient.mk_eq_mk,Submodule.Quotient.mk]
    congr 1
    refine FreeAlgebra.induction _ _ ?_ ?_ ?_ ?_ x
    · simp
    · simp[conj₁,conj₀_involutive]
    · simp +contextual
    · simp +contextual
  star_add := by
    apply Quotient.ind₂
    intro a b
    rw[←mk_eq_mk,←mk_eq_mk,←map_add,mk_eq_mk,mk_eq_mk, mk_eq_mk]
    simp [conj,Quotient.lift_mk,conj₂]
  star_mul := by
    apply Quotient.ind₂
    intro a b
    rw [←mk_eq_mk,←mk_eq_mk,←map_mul,mk_eq_mk,mk_eq_mk, mk_eq_mk,
      conj,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    simp[conj₂]

end conjugation

open conjugation in
theorem star_cre {α : Type} (x : α) : star (cre x) = ann x := by
  simp[star,conj,mk_eq_mk,conj₂,conj₁,conj₀]

open conjugation in
theorem star_ann {α : Type} (x : α) : star (ann x) = cre x := by
  simp[star,conj,mk_eq_mk,conj₂,conj₁,conj₀]

end Fock
