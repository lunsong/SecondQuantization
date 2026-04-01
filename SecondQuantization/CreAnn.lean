import Mathlib.Tactic

namespace SecondQuantization

variable (α R : Type) [Ring R]

def State := Finset α →₀ R

noncomputable instance State.addCommMonoid : AddCommMonoid (State α R) :=
  inferInstanceAs (AddCommMonoid (Finset α →₀ R))

noncomputable instance State.module : Module R (State α R) :=
  inferInstanceAs (Module R (Finset α →₀ R))

instance State.funLike : FunLike (State α R) (Finset α) R :=
  inferInstanceAs (FunLike (Finset α →₀ R) (Finset α) R)

theorem State.apply {φ : State α R} {s : Finset α} : φ s = φ.toFun s := rfl

theorem State.smul_toFun {φ : State α R} {a : R} : (a • φ).toFun = a • φ.toFun := rfl
theorem State.add_toFun {φ ψ : State α R} : (φ + ψ).toFun = φ.toFun + ψ.toFun := rfl

@[ext]
theorem State.ext {φ ψ : State α R} : (∀ s, φ s = ψ s) → φ = ψ := Finsupp.ext

def Operator := State α R →ₗ[R] State α R

variable {α R} [LinearOrder α] [NoZeroDivisors R]

namespace Fermion

def cre (x : α) : Operator α R where
  toFun φ := {
    toFun s :=
      if x ∈ s then
        if Even (Finset.card {y ∈ s | y < x}) then
          φ (s.erase x)
        else
          - φ (s.erase x)
      else 0
    support :=
      let s₀ : Finset (Finset α) := {s ∈ φ.support | x ∉ s}
      s₀.image fun s ↦ insert x s
    mem_support_toFun := by
      intro s
      constructor
      · simp only [Finset.mem_image, Finset.mem_filter, Finsupp.mem_support_iff, ne_eq,
          ite_eq_right_iff, Classical.not_imp, forall_exists_index, and_imp]
        intro s' h₁ h₂ h₃
        constructor
        · simp [← h₃]
        · rw [← h₃, Finset.erase_insert h₂]
          split <;> simpa
      · simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.mem_image, Finset.mem_filter,
          Finsupp.mem_support_iff, and_imp]
        intro h₁ h₂
        use s.erase x
        split_ands
        · intro hc
          simp [hc] at h₂
        · simp
        · exact Finset.insert_erase h₁
  }
  map_smul' a φ := by
    ext s
    simp [State.apply, State.smul_toFun]
  map_add' φ ψ := by
    ext s
    simp only [State.apply, State.add_toFun, Pi.add_apply, neg_add_rev]
    split_ifs
    · rfl
    · rw [add_comm]
    · rw [add_zero]

end Fermion

end SecondQuantization
