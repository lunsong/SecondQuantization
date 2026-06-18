import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import SecondQuantization.GTO.Defs

namespace GTO

open Real MeasureTheory

/-- The overlap of two s-type primitive GTOs sharing the same center is
  `∫ exp(-α‖r-R‖²) · exp(-β‖r-R‖²) dr = (√(π / (α + β)))^3`. -/
theorem overlap_primitiveGTO_s_same_center (α β : ℝ) (R : ℝ³) :
    overlap (primitiveGTO_s α R) (primitiveGTO_s β R) =
      (Real.sqrt (π / (α + β))) ^ 3 := by
  -- Reduce to a 3D Gaussian integral over r ↦ r - R
  have hsimp : ∀ r : ℝ³,
      primitiveGTO_s α R r * primitiveGTO_s β R r =
        Real.exp (-(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2) := by
    intro r
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero,
      Finset.prod_const_one, one_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  -- Translate r ↦ r + R so r - R becomes r
  have htrans :
      (∫ r : ℝ³, Real.exp (-(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2)) =
        ∫ r : ℝ³, Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r : ℝ³ => Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2)) R
    simp only at h
    rw [← h]
    simp only [Pi.sub_apply]
  -- Split exp of sum into product of exps; apply Fubini and 1D gaussian
  have hsplit : ∀ r : ℝ³,
      Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2) =
        ∏ i : Fin 3, Real.exp (-(α + β) * (r i) ^ 2) := by
    intro r
    rw [Finset.mul_sum, ← Real.exp_sum]
  -- Stitch everything together
  change (∫ r : ℝ³, primitiveGTO_s α R r * primitiveGTO_s β R r) = _
  conv_lhs =>
    arg 2; intro r
    rw [hsimp r]
  rw [htrans]
  conv_lhs =>
    arg 2; intro r
    rw [hsplit r]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-(α + β) * x ^ 2)),
      integral_gaussian]
  simp [Fintype.card_fin]

/-- **Gaussian product theorem.** The overlap of two s-type primitive GTOs centered at
different points `R₁`, `R₂` with exponents `α`, `β` (with `α + β ≠ 0`) is
  `(√(π / (α + β)))^3 · exp(-αβ/(α+β) · ‖R₁ - R₂‖²)`. -/
theorem overlap_primitiveGTO_s_diff_center (α β : ℝ) (hαβ : α + β ≠ 0)
    (R₁ R₂ : ℝ³) :
    overlap (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) =
      (Real.sqrt (π / (α + β))) ^ 3 *
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) := by
  -- Define the product center P = (α·R₁ + β·R₂) / (α+β)
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / (α + β) with hP
  -- Complete the square (sign-flipped form): -α(x-a)² - β(x-b)²
  --   = -αβ/(α+β)·(a-b)² - (α+β)·(x - (αa+βb)/(α+β))²
  have hsq : ∀ x a b : ℝ,
      -α * (x - a) ^ 2 + -β * (x - b) ^ 2
        = -(α * β) / (α + β) * (a - b) ^ 2
            + -(α + β) * (x - (α * a + β * b) / (α + β)) ^ 2 := by
    intro x a b
    field_simp
    ring
  -- Rewrite φα(r) * φβ(r) = exp(-αβ/(α+β)·‖R₁-R₂‖²) * exp(-(α+β)·∑(r-P)²)
  have hsimp : ∀ r : ℝ³,
      primitiveGTO_s α R₁ r * primitiveGTO_s β R₂ r =
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    intro r
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero,
      Finset.prod_const_one, one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have step : ∀ i : Fin 3,
        -α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2
          = -(α * β) / (α + β) * (R₁ i - R₂ i) ^ 2
              + -(α + β) * (r i - P i) ^ 2 := by
      intro i
      have hPi : P i = (α * R₁ i + β * R₂ i) / (α + β) := rfl
      rw [hPi]
      exact hsq (r i) (R₁ i) (R₂ i)
    calc -α * ∑ i : Fin 3, (r i - R₁ i) ^ 2
            + -β * ∑ i : Fin 3, (r i - R₂ i) ^ 2
        = ∑ i : Fin 3, (-α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α * β) / (α + β) * (R₁ i - R₂ i) ^ 2
              + -(α + β) * (r i - P i) ^ 2) :=
            Finset.sum_congr rfl (fun i _ => step i)
      _ = -(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2
              + -(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- The constant factor pulls out of the integral
  change (∫ r : ℝ³, primitiveGTO_s α R₁ r * primitiveGTO_s β R₂ r) = _
  conv_lhs =>
    arg 2; intro r
    rw [hsimp r]
  rw [MeasureTheory.integral_const_mul]
  -- Now reduce ∫ exp(-(α+β)·∑(r-P)²) to ∫ exp(-(α+β)·∑r²) by translation
  have htrans :
      (∫ r : ℝ³, Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2)) =
        ∫ r : ℝ³, Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r : ℝ³ => Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2)) P
    simp only at h
    rw [← h]
    simp only [Pi.sub_apply]
  rw [htrans]
  -- Split exp of sum into product of exps; apply Fubini and 1D gaussian
  have hsplit : ∀ r : ℝ³,
      Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2) =
        ∏ i : Fin 3, Real.exp (-(α + β) * (r i) ^ 2) := by
    intro r
    rw [Finset.mul_sum, ← Real.exp_sum]
  conv_lhs =>
    arg 2; arg 2; intro r
    rw [hsplit r]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-(α + β) * x ^ 2)),
      integral_gaussian]
  simp [Fintype.card_fin, mul_comm]

/-- Bilinearity of the overlap integral over the first argument: a finite sum can be pulled out,
provided each summand is integrable. -/
theorem overlap_finset_sum_left {ι : Type} [Fintype ι]
    (f : ι → ℝ³ → ℝ) (ψ : ℝ³ → ℝ)
    (hint : ∀ i, Integrable (fun r => f i r * ψ r)) :
    overlap (fun r => ∑ i : ι, f i r) ψ = ∑ i : ι, overlap (f i) ψ := by
  unfold overlap
  simp_rw [Finset.sum_mul]
  exact MeasureTheory.integral_finset_sum _ (fun i _ => hint i)

/-- Bilinearity of the overlap integral over the second argument. -/
theorem overlap_finset_sum_right {ι : Type} [Fintype ι]
    (φ : ℝ³ → ℝ) (g : ι → ℝ³ → ℝ)
    (hint : ∀ i, Integrable (fun r => φ r * g i r)) :
    overlap φ (fun r => ∑ i : ι, g i r) = ∑ i : ι, overlap φ (g i) := by
  unfold overlap
  simp_rw [Finset.mul_sum]
  exact MeasureTheory.integral_finset_sum _ (fun i _ => hint i)

/-- The overlap of two contracted s-type GTOs expands bilinearly into the Gaussian product
theorem over each pair of primitives. Requires `αᵢ + βⱼ ≠ 0` and integrability for every pair. -/
theorem overlap_contractedGTO_s {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (α : ι → ℝ) (R₁ : ℝ³)
    (d : κ → ℝ) (β : κ → ℝ) (R₂ : ℝ³)
    (hαβ : ∀ i j, α i + β j ≠ 0)
    (hint : ∀ i j, Integrable
      (fun r => primitiveGTO_s (α i) R₁ r * primitiveGTO_s (β j) R₂ r)) :
    overlap (contractedGTO c α R₁ 0) (contractedGTO d β R₂ 0) =
      ∑ i : ι, ∑ j : κ, c i * d j *
        ((Real.sqrt (π / (α i + β j))) ^ 3 *
          Real.exp (-(α i * β j) / (α i + β j) *
            ∑ k : Fin 3, (R₁ k - R₂ k) ^ 2)) := by
  -- Unfold contractedGTO and pull the sums out
  have hexpand : ∀ r : ℝ³,
      contractedGTO c α R₁ 0 r * contractedGTO d β R₂ 0 r
        = ∑ i : ι, ∑ j : κ,
            c i * d j * (primitiveGTO_s (α i) R₁ r * primitiveGTO_s (β j) R₂ r) := by
    intro r
    simp only [contractedGTO, primitiveGTO_s]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  unfold overlap
  conv_lhs =>
    arg 2; intro r
    rw [hexpand r]
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset ι)
        (fun i _ => MeasureTheory.integrable_finset_sum _
          (fun j _ => ((hint i j).const_mul (c i * d j))))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset κ)
        (fun j _ => (hint i j).const_mul (c i * d j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [MeasureTheory.integral_const_mul, ← overlap]
  rw [overlap_primitiveGTO_s_diff_center (α i) (β j) (hαβ i j) R₁ R₂]


end GTO
