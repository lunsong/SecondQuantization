import Mathlib.Tactic

namespace SecondQuantization

variable (α R : Type) [CommRing R]

def Operator := (Finset α → R) →ₗ[R] (Finset α → R)

instance Operator

@[ext]
theorem Operator.ext {A B : Operator α R} : (∀ φ, A φ = B φ) → A = B := LinearMap.ext

instance Operator.semiring : Ring (Operator α R) :=
  inferInstanceAs (Ring ((Finset α → R) →ₗ[R] (Finset α → R)))

--instance Operator.algebra : Algebra R (Operator α R) :=
--  inferInstanceAs (Algebra R ((Finset α → R) →ₗ[R] (Finset α → R)))

variable {α} [LinearOrder α] [NoZeroDivisors R]

namespace Fermion

def cre (x : α) : Operator α R where
  toFun φ s := 
    if x ∈ s then
      if Even (Finset.card {y ∈ s | y < x}) then
        φ (s.erase x)
      else
        - φ (s.erase x)
    else 0
  map_smul' a φ := by
    ext s
    simp
  map_add' φ ψ := by
    ext s
    simp only [Pi.add_apply, neg_add_rev]
    split_ifs
    · rfl
    · rw [add_comm]
    · rw [add_zero]

def ann (x : α) : Operator α R where
  toFun φ s := 
    if x ∉ s then
      if Even (Finset.card {y ∈ s | y < x}) then
        φ (insert x s)
      else
        - φ (insert x s)
    else 0
  map_smul' a φ := by
    ext s
    simp
  map_add' φ ψ := by
    ext s
    simp only [Pi.add_apply, neg_add_rev]
    split_ifs
    · rw [add_zero]
    · rfl
    · rw [add_comm]

theorem cre_ann {x y : α} : cre R x * ann R y + ann R y * cre R x = if x = y then 1 else 0 := by
  split_ifs with h
  · cases h
    ext s

end Fermion

end SecondQuantization
