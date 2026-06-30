import Mathlib.Tactic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import SecondQuantization.CreAnn.Basic

namespace Fermion

variable {R : Type} [RCLike R]

theorem ContinuousLinearMap.exp_eq_of_pow_eq {A B : Type}
  [NormedRing A] [NormedAlgebra R A] [CompleteSpace A]
  [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra R B] [T2Space B]
  {X : A} {Y : B} {f : A →L[R] B} (h : ∀ n : ℕ, f (X ^ n) = Y ^ n) :
    f (NormedSpace.exp X) = NormedSpace.exp Y := by
  simp only [NormedSpace.exp_eq_tsum R]
  rw [ContinuousLinearMap.map_tsum]
  · congr
    ext n
    rw [map_smul, h]
  use NormedSpace.exp X
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := R) X

theorem ContinuousLinearMap.exp_eq_of_pow_eq' {A B C : Type}
  [TopologicalSpace C] [AddCommMonoid C] [Module R C] [T2Space C]
  [NormedRing A] [NormedAlgebra R A] [IsTopologicalRing A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra R B] [IsTopologicalRing B] [CompleteSpace B]
  {f : A →L[R] C} {g : B →L[R] C} {x : A} {y : B}
  (h : ∀ n : ℕ, f (x ^ n) = g (y ^ n)) :
    f (NormedSpace.exp x) = g (NormedSpace.exp y) := by
  simp only [NormedSpace.exp_eq_tsum R]
  repeat rw [ContinuousLinearMap.map_tsum]
  · congr; ext n; simp [map_smul, h]
  · exact ⟨NormedSpace.exp y, NormedSpace.exp_series_hasSum_exp' y⟩
  · exact ⟨NormedSpace.exp x, NormedSpace.exp_series_hasSum_exp' x⟩

@[continuity]
theorem Matrix.continuous_apply {ι : Type}
  (i j : ι) : Continuous fun (M : Matrix ι ι R) ↦ M i j := by
  change Continuous ((fun x ↦ x j) ∘ (fun (M : Matrix ι ι R) ↦ M i))
  apply Continuous.comp <;> apply _root_.continuous_apply

set_option maxHeartbeats 0 in
-- necessary
set_option synthInstance.maxHeartbeats 0 in
theorem exp_adj {α : Type} [Fintype α] (A : Operator α R)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (x : ι → Operator α R) (K : Matrix ι ι R)
  (h : ∀ i, A * x i - x i * A = ∑ j, K i j • x j) :
    ∀ i, NormedSpace.exp A * x i * NormedSpace.exp (-A) = ∑ j, (NormedSpace.exp K) i j • x j := by
  let A_left := ContinuousLinearMap.mul R (Operator α R) A
  let A_right := (ContinuousLinearMap.mul R (Operator α R)).flip (-A)
  have h_commute : Commute A_left A_right := by ext1 X; simp [A_left, A_right, mul_assoc]
  haveI : NormedAlgebra ℚ (Operator α R →L[R] Operator α R) :={
    norm_smul_le _ _ := ContinuousLinearMap.opNorm_smul_le _ _
  }
  haveI : CompleteSpace (Operator α R →L[R] Operator α R) :=
    FiniteDimensional.complete R (Operator α R →L[R] Operator α R)
  have h1 := NormedSpace.exp_add_of_commute h_commute
  have h_exp_A_left : NormedSpace.exp A_left =
      ContinuousLinearMap.mul R (Operator α R) (NormedSpace.exp A) := by
    apply Eq.symm
    apply ContinuousLinearMap.exp_eq_of_pow_eq
    intro n
    ext1 X
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      simp only [ContinuousLinearMap.mul_apply'] at ih ⊢
      rw [add_comm, pow_add, pow_one, mul_assoc, ih, pow_add, pow_one]
      simp only [ContinuousLinearMap.coe_mul, Function.comp_apply, ContinuousLinearMap.mul_apply',
        A_left]
  have h_exp_A_right : NormedSpace.exp A_right =
      (ContinuousLinearMap.mul R (Operator α R)).flip (NormedSpace.exp (-A)) := by
    apply Eq.symm
    apply ContinuousLinearMap.exp_eq_of_pow_eq
    intro n
    ext1 X
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at ih ⊢
      rw [pow_succ, ← mul_assoc, ih, add_comm, pow_add, pow_one]
      simp only [ContinuousLinearMap.coe_mul, Function.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', A_right]
  intro i
  let φ : (Matrix ι ι R) →L[R] Operator α R := {
    toFun M := ∑ j, M i j • x j
    map_add' M N := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' k M := by simp only [Matrix.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum]
  }
  let ad := A_left + A_right
  have h_exp_ad : φ (NormedSpace.exp K) =
      ContinuousLinearMap.apply R (Operator α R) (x i) (NormedSpace.exp ad) := by
    open scoped Matrix.Norms.Operator in apply ContinuousLinearMap.exp_eq_of_pow_eq'
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.apply_apply, φ]
    intro n
    revert i
    simp only
    induction n with
    | zero => simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      conv_rhs =>
        rw [pow_succ, ContinuousLinearMap.mul_apply]
        arg 2
        equals ∑ j, K i j • x j =>
          simp [ad, A_left, A_right, ← sub_eq_add_neg, h]
      rw [map_sum, add_comm, pow_add, pow_one]
      conv_rhs =>
        arg 2; intro j; rw [map_smul, ← ih, Finset.smul_sum]
        arg 2; intro k; rw [smul_smul]
      rw [Finset.sum_comm]
      congr
      ext1 j
      rw [← Finset.sum_smul]
      rfl
  rw [mul_assoc]
  trans (NormedSpace.exp A_left * NormedSpace.exp A_right) (x i)
  · simp [h_exp_A_left, h_exp_A_right]
  · rw [← h1]; exact h_exp_ad.symm

end Fermion
