import SecondQuantization.GTO.Overlap

/-!
# Gaussian moments, general-angular-momentum overlap, and the kinetic-energy integral

This file proves three families of results used throughout the GTO directory:

1. **Gaussian moment integrals.** `integral_gaussian_moment_1d` gives the closed form
   `∫ x^n exp(-γ x²) dx = (n-1)‼ · √(π/γ) / (2γ)^(n/2)` for even `n` (and `0` for odd `n`),
   proved by strong induction on `n` via the integration-by-parts recurrence
   `I_{m+2} = (m+1)/(2γ) · I_m`. This is the engine behind every higher-angular-momentum
   integral.

2. **General angular-momentum overlap.** `overlap_primitiveGTO_same_center` factors the overlap
   of two same-center primitives into a product of 1D moments; `overlap_primitiveGTO_diff_center`
   translates to the Gaussian product center `P` and leaves 1D moments; `overlap_primitiveGTO`
   expands these fully via the binomial theorem into a finite sum of `gaussianMoment` values.

3. **s-type kinetic-energy integral.** Using the Fréchet derivative of an s-type GTO
   (`fderiv_primitiveGTO_s`), `kinetic_primitiveGTO_s_same_center` and
   `kinetic_primitiveGTO_s_diff_center` give the closed forms of `½ ∫ ∇φ · ∇ψ`.

The nuclear-attraction and electron-repulsion integrals (which reduce to the Boys function) live
in `Coulomb.lean`.
-/

namespace GTO

open Real MeasureTheory

/-! ## Gaussian moment integrals -/

/-- The one-dimensional Gaussian even-moment formula:
  `M(2k, γ) = (2k-1)!! · √(π/γ) / (2γ)^k`. Odd moments vanish by symmetry. -/
noncomputable def gaussianMoment (n : ℕ) (γ : ℝ) : ℝ :=
  if n % 2 = 1 then 0
  else (Nat.doubleFactorial (n - 1) : ℝ) * Real.sqrt (π / γ) / (2 * γ) ^ (n / 2)

/-- The 1D Gaussian moment integral equals `gaussianMoment n γ` for `γ > 0`:
  `∫ x^n · exp(-γ x²) dx = (n-1)‼ · √(π/γ) / (2γ)^(n/2)` for even `n`, and `0` for odd `n`.

The proof is by strong induction on `n`. The inductive step uses the integration-by-parts
recurrence `I_{m+2} = (m+1)/(2γ) · I_m`, obtained by integrating the derivative of
`x^(m+1) · exp(-γ x²)` (whose boundary terms vanish at `±∞`); the odd case vanishes by the
symmetry `x ↦ -x`. -/
lemma integral_gaussian_moment_1d (n : ℕ) (γ : ℝ) (hγ : γ > 0) :
    ∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2) = gaussianMoment n γ := by
  -- Integrability of x^k * exp(-γ x²) on ℝ for any k : ℕ
  have h_int (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (-γ * x ^ 2)) volume := by
    have hk : (-1 : ℝ) < (k : ℝ) := by
      have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq hγ hk
    simpa [Real.rpow_natCast] using h
  -- Algebraic identity for gaussianMoment: recurrence in the even/odd case
  have h_gm_recurrence (m : ℕ) : gaussianMoment (m + 2) γ =
      ((m + 1 : ℝ) / (2 * γ)) * gaussianMoment m γ := by
    dsimp [gaussianMoment]
    by_cases hm : m % 2 = 1
    · have hm2 : (m + 2) % 2 = 1 := by
        rw [Nat.add_mod_right]; simpa using hm
      simp [hm, hm2]
    · have hm_even : m % 2 = 0 := Nat.mod_two_eq_zero_or_one m |>.resolve_right hm
      have hm2_even : (m + 2) % 2 = 0 := by
        rw [Nat.add_mod_right]; simpa using hm_even
      simp [hm_even, hm2_even]
      have h_df : (Nat.doubleFactorial (m + 1) : ℝ) =
          (m + 1 : ℝ) * (Nat.doubleFactorial (m - 1) : ℝ) := by
        simp [Nat.doubleFactorial_add_one m]
      rw [h_df]
      have h_pow : (2 * γ : ℝ) ^ (m / 2 + 1) = (2 * γ : ℝ) * (2 * γ : ℝ) ^ (m / 2) := by
        rw [pow_succ, mul_comm]
      rw [h_pow]
      field_simp [show 2 * γ ≠ 0 by linarith]
  -- Integral recurrence: I_{m+2} = ((m+1)/(2γ)) * I_m, using derivative method
  have h_int_recurrence (m : ℕ) : (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
      ((m + 1 : ℝ) / (2 * γ)) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by
    set f := fun x : ℝ => x ^ (m + 1) * Real.exp (-γ * x ^ 2) with hf_def
    set f1 := fun x : ℝ => ((m + 1 : ℝ) * x ^ m * Real.exp (-γ * x ^ 2)) with hf1_def
    set f2 := fun x : ℝ => (2 * γ) * x ^ (m + 2) * Real.exp (-γ * x ^ 2) with hf2_def
    set f' := fun x : ℝ => f1 x - f2 x with hf'_def
    -- Derivative: f' = d/dx f
    have h_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
      intro x
      dsimp [f, f', f1, f2]
      have h1 : HasDerivAt (fun x : ℝ => x ^ (m + 1)) ((m + 1 : ℝ) * x ^ m) x := by
        have h := hasDerivAt_pow (m + 1) x
        simpa [show ((m + 1 : ℕ) - 1 : ℕ) = m by omega, Nat.cast_succ] using h
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-γ * x ^ 2))
          (Real.exp (-γ * x ^ 2) * (-2 * γ * x)) x := by
        have h_inner : HasDerivAt (fun x : ℝ => -γ * x ^ 2) (-2 * γ * x) x := by
          have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
            simpa using hasDerivAt_pow 2 x
          simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using h_sq.const_mul (-γ)
        exact (Real.hasDerivAt_exp (-γ * x ^ 2)).comp x h_inner
      have h_mul := h1.mul h2
      convert h_mul using 1
      ring
    -- Integrability conditions
    have h_int_f : Integrable f volume := by dsimp [f]; simpa using h_int (m + 1)
    have h_int_f1 : Integrable f1 volume := by
      dsimp [f1]; simpa [mul_assoc] using (h_int m).const_mul (m + 1 : ℝ)
    have h_int_f2 : Integrable f2 volume := by
      dsimp [f2]; simpa [mul_assoc] using (h_int (m + 2)).const_mul (2 * γ)
    have h_int_f' : Integrable f' volume := by
      dsimp [f']; exact Integrable.sub h_int_f1 h_int_f2
    -- ∫ f' = 0 by fundamental theorem of calculus (boundary terms vanish at ±∞)
    have h_zero : (∫ x : ℝ, f' x) = 0 :=
      MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable h_deriv h_int_f' h_int_f
    -- Expand: ∫ f' = (m+1)*I_m - (2γ)*I_{m+2}
    have h_expanded : (∫ x : ℝ, f' x) = (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) -
        (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by
      dsimp [f', f1, f2]
      rw [integral_sub h_int_f1 h_int_f2]
      have h_int1 : (∫ x : ℝ, ((m + 1 : ℝ) * x ^ m * Real.exp (-γ * x ^ 2))) =
          (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by
        calc
          (∫ x : ℝ, ((m + 1 : ℝ) * x ^ m * Real.exp (-γ * x ^ 2))) =
              (∫ x : ℝ, (m + 1 : ℝ) * (x ^ m * Real.exp (-γ * x ^ 2))) := by
            refine integral_congr_ae ?_; filter_upwards with x; ring
          _ = (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by
            rw [integral_const_mul]
      have h_int2 : (∫ x : ℝ, (2 * γ) * x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
          (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by
        calc
          (∫ x : ℝ, (2 * γ) * x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
              (∫ x : ℝ, (2 * γ) * (x ^ (m + 2) * Real.exp (-γ * x ^ 2))) := by
            refine integral_congr_ae ?_; filter_upwards with x; ring
          _ = (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by
            rw [integral_const_mul]
      rw [h_int1, h_int2]
    rw [h_expanded] at h_zero
    -- Rearrange: (m+1)*I_m = (2γ)*I_{m+2} → I_{m+2} = (m+1)/(2γ) * I_m
    have h_eq : (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) =
        (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by linarith
    have h_denom : 2 * γ ≠ 0 := by linarith
    calc
      (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
          ((2 * γ)⁻¹) * ((2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2))) := by
        field_simp [h_denom]
      _ = ((2 * γ)⁻¹) * ((m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2))) := by rw [h_eq]
      _ = ((m + 1 : ℝ) / (2 * γ)) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by ring
  -- Main proof: strong induction on n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn_odd : n % 2 = 1
  · -- Odd n: integral = 0 by symmetry, gaussianMoment n γ = 0 by definition
    have h_gm : gaussianMoment n γ = 0 := by
      dsimp [gaussianMoment]; simp [hn_odd]
    rw [h_gm]
    -- Show integral = 0 by f(-x) = -f(x) for odd n
    have h_main : (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) =
        - (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) := by
      have h_eq : (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) =
          (∫ x : ℝ, (-x) ^ n * Real.exp (-γ * (-x) ^ 2)) := by
        rw [integral_neg_eq_self (fun x => x ^ n * Real.exp (-γ * x ^ 2)) volume]
      have h_neg_pow : ∀ x : ℝ, (-x) ^ n = -(x ^ n) := by
        intro x
        have h_odd : Odd n := Nat.odd_iff.mpr hn_odd
        calc
          (-x) ^ n = ((-1 : ℝ) * x) ^ n := by ring
          _ = (-1 : ℝ) ^ n * x ^ n := by ring
          _ = (-1 : ℝ) * x ^ n := by rw [Odd.neg_one_pow h_odd]
          _ = -(x ^ n) := by ring
      calc
        (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) =
            (∫ x : ℝ, (-x) ^ n * Real.exp (-γ * (-x) ^ 2)) := h_eq
        _ = (∫ x : ℝ, (-(x ^ n)) * Real.exp (-γ * x ^ 2)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          simp [h_neg_pow x, show (-x) ^ 2 = x ^ 2 by ring]
        _ = (∫ x : ℝ, -(x ^ n * Real.exp (-γ * x ^ 2))) := by
          refine integral_congr_ae ?_
          filter_upwards with x; ring
        _ = - (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) := by rw [integral_neg]
    linarith
  · -- Even n: handle n=0 directly, or use recurrence for n ≥ 2
    have hn_even : n % 2 = 0 := Nat.mod_two_eq_zero_or_one n |>.resolve_right hn_odd
    by_cases hn0 : n = 0
    · subst hn0
      simp [gaussianMoment]
      simpa [neg_mul] using integral_gaussian γ
    by_cases hn1 : n = 1
    · subst hn1; norm_num at hn_even
    -- n ≥ 2: write n = m + 2, apply recurrence and induction hypothesis
    have hn_ge2 : 2 ≤ n := by omega
    rcases Nat.exists_eq_add_of_le hn_ge2 with ⟨m, hm⟩
    rw [show n = m + 2 by omega] at ih ⊢
    calc
      (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
          ((m + 1 : ℝ) / (2 * γ)) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) :=
        h_int_recurrence m
      _ = ((m + 1 : ℝ) / (2 * γ)) * gaussianMoment m γ := by rw [ih m (by omega)]
      _ = gaussianMoment (m + 2) γ := by rw [h_gm_recurrence m]

/-! ## General angular-momentum overlap -/

/-- The overlap of two same-center primitive GTOs with general angular momenta `l`, `m` factors
into a product of one-dimensional Gaussian moments of total degree `lᵢ + mᵢ`.
Requires `α + β > 0` so that the Gaussian integrals converge. -/
theorem overlap_primitiveGTO_same_center (α β : ℝ) (R : ℝ³) (l m : Fin 3 → ℕ) (hαβ : α + β > 0) :
    overlap (primitiveGTO α R l) (primitiveGTO β R m) =
      ∏ i : Fin 3, gaussianMoment (l i + m i) (α + β) := by
  unfold overlap primitiveGTO
  -- Simplify the integrand to a product of 1D factors
  have hsimp : ∀ r : ℝ³,
      ((∏ i : Fin 3, (r i - R i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2)) *
        ((∏ i : Fin 3, (r i - R i) ^ m i) * Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) =
        ∏ i : Fin 3, ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2)) := by
    intro r
    calc
      ((∏ i : Fin 3, (r i - R i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2)) *
          ((∏ i : Fin 3, (r i - R i) ^ m i) * Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) =
          ((∏ i : Fin 3, (r i - R i) ^ l i) * (∏ i : Fin 3, (r i - R i) ^ m i)) *
            (Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2) *
              Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) := by ring
      _ = ((∏ i : Fin 3, ((r i - R i) ^ l i * (r i - R i) ^ m i))) *
            (Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2) *
              Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) := by
        rw [← Finset.prod_mul_distrib]
      _ = ((∏ i : Fin 3, ((r i - R i) ^ l i * (r i - R i) ^ m i))) *
            Real.exp ((-α * ∑ i : Fin 3, (r i - R i) ^ 2) +
              (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) := by rw [Real.exp_add]
      _ = (∏ i : Fin 3, ((r i - R i) ^ l i * (r i - R i) ^ m i)) *
            Real.exp (-(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2) := by
        have h : (-α * ∑ i : Fin 3, (r i - R i) ^ 2) + (-β * ∑ i : Fin 3, (r i - R i) ^ 2) =
            -(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2 := by ring
        rw [h]
      _ = (∏ i : Fin 3, ((r i - R i) ^ (l i + m i))) *
            Real.exp (-(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2) := by
        refine congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
        rw [pow_add]
      _ = (∏ i : Fin 3, ((r i - R i) ^ (l i + m i))) *
            Real.exp (∑ i : Fin 3, (-(α + β) * (r i - R i) ^ 2)) := by
        rw [Finset.mul_sum]
      _ = (∏ i : Fin 3, ((r i - R i) ^ (l i + m i))) *
            (∏ i : Fin 3, Real.exp (-(α + β) * (r i - R i) ^ 2)) := by
        rw [Real.exp_sum]
      _ = ∏ i : Fin 3, ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2)) := by
        rw [Finset.prod_mul_distrib]
  -- Rewrite the integral using hsimp
  have h_int_eq : (∫ r : ℝ³,
      ((∏ i : Fin 3, (r i - R i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2)) *
        ((∏ i : Fin 3, (r i - R i) ^ m i) * Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2))) =
      (∫ r : ℝ³, ∏ i : Fin 3,
        ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2))) := by
    refine integral_congr_ae ?_
    filter_upwards with r
    rw [hsimp r]
  rw [h_int_eq]
  -- Translate r ↦ r + R (so r - R becomes r)
  have h_trans : (∫ r : ℝ³, ∏ i : Fin 3,
      ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2))) =
      (∫ r : ℝ³, ∏ i : Fin 3,
        (r i ^ (l i + m i) * Real.exp (-(α + β) * (r i) ^ 2))) := by
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r : ℝ³ => ∏ i : Fin 3,
        (r i ^ (l i + m i) * Real.exp (-(α + β) * (r i) ^ 2))) R
    simpa [Pi.sub_apply] using this
  rw [h_trans]
  -- Factor the 3D integral into product of 1D integrals
  rw [integral_fintype_prod_volume_eq_prod
    (fun (i : Fin 3) (x : ℝ) => x ^ (l i + m i) * Real.exp (-(α + β) * x ^ 2))]
  -- Each 1D integral equals gaussianMoment (l_i + m_i) (α+β) by integral_gaussian_moment_1d
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_gaussian_moment_1d (l i + m i) (α + β) hαβ]

/-- The overlap of two different-center primitive GTOs with general angular momenta factors,
after translation to the product center `P = (αR₁ + βR₂)/(α+β)`, into a product over the three
axes of one-dimensional moment integrals of the form
  `∫ (x + Pᵢ - R₁ᵢ)^(lᵢ) · (x + Pᵢ - R₂ᵢ)^(mᵢ) · exp(-(α+β)·x²) dx`,
with an overall pre-factor `exp(-αβ/(α+β)·‖R₁-R₂‖²)` from the Gaussian product theorem. The
fully-expanded McMurchie–Davidson form would express these one-dimensional moments as finite
linear combinations of `gaussianMoment k (α+β)`. -/
theorem overlap_primitiveGTO_diff_center (α β : ℝ) (_ : α + β ≠ 0)
    (R₁ R₂ : ℝ³) (l m : Fin 3 → ℕ) :
    overlap (primitiveGTO α R₁ l) (primitiveGTO β R₂ m) =
      Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        ∏ i : Fin 3, ∫ x : ℝ,
          (x + (α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i) *
          (x + (α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i) *
          Real.exp (-(α + β) * x ^ 2) := by
  -- Gaussian product center P = (α·R₁ + β·R₂) / (α+β)
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / (α + β) with hP
  -- Completing the square identity (1D)
  have hsq : ∀ x a b : ℝ,
      -α * (x - a) ^ 2 + -β * (x - b) ^ 2
        = -(α * β) / (α + β) * (a - b) ^ 2
            + -(α + β) * (x - (α * a + β * b) / (α + β)) ^ 2 := by
    intro x a b
    field_simp
    ring
  -- Lift to 3D: equality of the exponent sums
  have h_exp_sum_eq : ∀ r : ℝ³,
      (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) + (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2)
        = (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2)
          + (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    intro r
    have step : ∀ i : Fin 3,
        -α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2
          = -(α * β) / (α + β) * (R₁ i - R₂ i) ^ 2
              + -(α + β) * (r i - P i) ^ 2 := by
      intro i
      have hPi : P i = (α * R₁ i + β * R₂ i) / (α + β) := rfl
      rw [hPi]
      exact hsq (r i) (R₁ i) (R₂ i)
    calc
      (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) + (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2)
          = ∑ i : Fin 3, (-α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α * β) / (α + β) * (R₁ i - R₂ i) ^ 2
              + -(α + β) * (r i - P i) ^ 2) :=
            Finset.sum_congr rfl (fun i _ => step i)
      _ = (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2)
            + (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Rewrite the integrand: factor into constant * (poly prod) * translated Gaussian
  have hsimp : ∀ r : ℝ³,
      primitiveGTO α R₁ l r * primitiveGTO β R₂ m r =
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          (∏ i : Fin 3, (r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
          Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    intro r
    simp only [primitiveGTO]
    calc
      ((∏ i : Fin 3, (r i - R₁ i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2)) *
          ((∏ i : Fin 3, (r i - R₂ i) ^ m i) * Real.exp (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2))
      = ((∏ i : Fin 3, (r i - R₁ i) ^ l i) * (∏ i : Fin 3, (r i - R₂ i) ^ m i)) *
          (Real.exp (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) *
            Real.exp (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2)) := by
        ring
      _ = ((∏ i : Fin 3, (r i - R₁ i) ^ l i) * (∏ i : Fin 3, (r i - R₂ i) ^ m i)) *
          Real.exp ((-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) +
            (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2)) := by
        rw [Real.exp_add]
      _ = ((∏ i : Fin 3, (r i - R₁ i) ^ l i) * (∏ i : Fin 3, (r i - R₂ i) ^ m i)) *
          Real.exp ((-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) +
            (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2)) := by
        rw [h_exp_sum_eq r]
      _ = Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          ((∏ i : Fin 3, (r i - R₁ i) ^ l i) * (∏ i : Fin 3, (r i - R₂ i) ^ m i)) *
          Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          (∏ i : Fin 3, ((r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i)) *
          Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
        rw [Finset.prod_mul_distrib]
  unfold overlap
  conv_lhs =>
    arg 2; intro r
    rw [hsimp r, mul_assoc]
  -- Pull out the constant factor (independent of r)
  rw [MeasureTheory.integral_const_mul]
  -- Now the target is: C * I = C * RHS where C = exp(...), I = ∫ poly*exp, RHS = ∏∫...
  -- Factor the integral I into a product-of-1D-integrals, then translate each 1D integral
  congr 2
  -- Show I = RHS (without the C factor)
  have hsplit : ∀ r : ℝ³,
      Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) =
        ∏ i : Fin 3, Real.exp (-(α + β) * (r i - P i) ^ 2) := by
    intro r
    rw [Finset.mul_sum, ← Real.exp_sum]
  -- Rewrite integrand: (∏ poly) * exp_sum = ∏ (poly * exp_i)
  have hintegrand_eq :
      (fun r : ℝ³ => (∏ i : Fin 3, (r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2)) =
      (fun r : ℝ³ => ∏ i : Fin 3, (((r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * (r i - P i) ^ 2))) := by
    ext r
    rw [hsplit r]
    simp [Finset.prod_mul_distrib, mul_assoc]
  calc
    (∫ r : ℝ³, (∏ i : Fin 3, (r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2))
    = (∫ r : ℝ³, ∏ i : Fin 3, (((r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * (r i - P i) ^ 2))) := by
      rw [hintegrand_eq]
    _ = ∏ i : Fin 3, ∫ x : ℝ, ((x - R₁ i) ^ l i * (x - R₂ i) ^ m i) *
        Real.exp (-(α + β) * (x - P i) ^ 2) :=
      integral_fintype_prod_volume_eq_prod
        (fun i x => ((x - R₁ i) ^ l i * (x - R₂ i) ^ m i) *
          Real.exp (-(α + β) * (x - P i) ^ 2))
    _ = ∏ i : Fin 3, ∫ x : ℝ, (x + P i - R₁ i) ^ l i * (x + P i - R₂ i) ^ m i *
        Real.exp (-(α + β) * x ^ 2) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have h1d := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
        (fun x : ℝ => (x + P i - R₁ i) ^ l i * (x + P i - R₂ i) ^ m i *
          Real.exp (-(α + β) * x ^ 2)) (P i)
      simpa [sub_add_cancel] using h1d
    _ = ∏ i : Fin 3, ∫ x : ℝ,
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ l i *
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ m i *
        Real.exp (-(α + β) * x ^ 2) := by
      simp [P]

/-- Fully expanded form of `overlap_primitiveGTO_diff_center` via the binomial theorem.
Each one-dimensional integral `∫ (x + Aᵢ)^(lᵢ) · (x + Bᵢ)^(mᵢ) · exp(-γ·x²) dx` is expanded as

  Σ_{p=0}^{lᵢ} Σ_{q=0}^{mᵢ} binom(lᵢ, p) · binom(mᵢ, q) · Aᵢ^(lᵢ-p) · Bᵢ^(mᵢ-q) · M(p+q, γ)

where `γ = α+β`, `Aᵢ = Pᵢ - R₁ᵢ = β·(R₂ᵢ - R₁ᵢ)/(α+β)`,
`Bᵢ = Pᵢ - R₂ᵢ = α·(R₁ᵢ - R₂ᵢ)/(α+β)`,
`Pᵢ = (α·R₁ᵢ + β·R₂ᵢ)/(α+β)` is the Gaussian product center, and
`M(k, γ) = gaussianMoment k γ` is the closed-form Gaussian moment integral.

Requires `α + β > 0` to apply `integral_gaussian_moment_1d`. -/
theorem overlap_primitiveGTO (α β : ℝ) (hpos : α + β > 0) (R₁ R₂ : ℝ³) (l m : Fin 3 → ℕ) :
    overlap (primitiveGTO α R₁ l) (primitiveGTO β R₂ m) =
      Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        ∏ i : Fin 3,
          (∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
            ((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
            (((α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i - p)) *
            (((α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i - q)) *
            gaussianMoment (p + q) (α + β)) := by
  rw [overlap_primitiveGTO_diff_center α β hpos.ne.symm R₁ R₂ l m]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  let γ := α + β
  have hγpos : γ > 0 := hpos
  have hint (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (-γ * x ^ 2)) volume := by
    have hk : (-1 : ℝ) < (k : ℝ) := by
      have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq hγpos hk
    simpa [Real.rpow_natCast] using h
  have h_one_axis :
      (∫ x : ℝ,
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i) *
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i) *
        Real.exp (-γ * x ^ 2)) =
      (∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
        ((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
        (((α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i - p)) *
        (((α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i - q)) *
        gaussianMoment (p + q) γ) := by
    set A := (α * R₁ i + β * R₂ i) / (α + β) - R₁ i with hA
    set B := (α * R₁ i + β * R₂ i) / (α + β) - R₂ i with hB
    have h_poly (x : ℝ) : (x + A) ^ (l i) * (x + B) ^ (m i) =
        ∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
          (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
            A ^ (l i - p) * B ^ (m i - q)) * x ^ (p + q) := by
      rw [add_pow, add_pow]
      simp_rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      ring
    have hint' (k : ℕ) (C : ℝ) :
        Integrable (fun x : ℝ => C * (x ^ k * Real.exp (-γ * x ^ 2))) volume :=
      (hint k).const_mul C
    have h_integrand : (fun x : ℝ => (x + A) ^ (l i) * (x + B) ^ (m i) * Real.exp (-γ * x ^ 2)) =
        (fun x : ℝ => ∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
          (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
            A ^ (l i - p) * B ^ (m i - q)) * (x ^ (p + q) * Real.exp (-γ * x ^ 2))) := by
      ext x
      calc
        (x + A) ^ (l i) * (x + B) ^ (m i) * Real.exp (-γ * x ^ 2) =
            ((x + A) ^ (l i) * (x + B) ^ (m i)) * Real.exp (-γ * x ^ 2) := by ring
        _ = (∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
              (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
                A ^ (l i - p) * B ^ (m i - q)) * x ^ (p + q)) *
            Real.exp (-γ * x ^ 2) := by rw [h_poly x]
        _ = ∑ p ∈ Finset.range (l i + 1), ∑ q ∈ Finset.range (m i + 1),
              (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
                A ^ (l i - p) * B ^ (m i - q)) * (x ^ (p + q) * Real.exp (-γ * x ^ 2)) := by
          simp [Finset.sum_mul, mul_assoc]
    have h_rewrite_AB : (fun x : ℝ =>
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i) *
        (x + (α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i) *
        Real.exp (-γ * x ^ 2)) =
        (fun x : ℝ => (x + A) ^ (l i) * (x + B) ^ (m i) * Real.exp (-γ * x ^ 2)) := by
      ext x; dsimp [A, B]; ring
    rw [h_rewrite_AB, h_integrand]
    rw [integral_finset_sum (Finset.range (l i + 1))
      (f := fun p x => ∑ q ∈ Finset.range (m i + 1),
        (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
          A ^ (l i - p) * B ^ (m i - q)) * (x ^ (p + q) * Real.exp (-γ * x ^ 2)))
      (fun p _ => integrable_finset_sum (Finset.range (m i + 1))
        (fun q _ => hint' (p + q) (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
          A ^ (l i - p) * B ^ (m i - q))))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [integral_finset_sum (Finset.range (m i + 1))
      (f := fun q x => (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
        A ^ (l i - p) * B ^ (m i - q)) * (x ^ (p + q) * Real.exp (-γ * x ^ 2)))
      (fun q _ => hint' (p + q) (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
        A ^ (l i - p) * B ^ (m i - q)))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_const_mul (((l i).choose p : ℝ) * ((m i).choose q : ℝ) *
      A ^ (l i - p) * B ^ (m i - q)),
      integral_gaussian_moment_1d (p + q) γ hγpos]
  dsimp [γ] at h_one_axis
  simpa using h_one_axis

/-! ## First derivative of s-type GTOs -/

open ContinuousLinearMap

local notation "π[" i "]" => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

/-- Application of a sum of scaled projections to `Pi.single i 1`. -/
lemma proj_sum_apply_single (a : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j : Fin 3, a j • π[j]) (Pi.single i (1 : ℝ)) = a i := by
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Pi.single_apply]

/-- The Fréchet derivative of `primitiveGTO_s α R` at `r`. -/
lemma fderiv_primitiveGTO_s (α : ℝ) (R r : ℝ³) :
    fderiv ℝ (primitiveGTO_s α R) r =
      (primitiveGTO_s α R r) • (∑ i : Fin 3, ((-2 * α) * (r i - R i)) • π[i]) := by
  have h_sq (i : Fin 3) : fderiv ℝ (fun (r' : ℝ³) => (r' i - R i) ^ 2) r =
      (2 * (r i - R i)) • π[i] := by
    have h := (π[i]).hasFDerivAt (x := r)
    have h_sq := ((h.sub_const (R i)).pow 2).fderiv
    simpa [pow_one] using h_sq
  have h_sq_diff (i : Fin 3) : DifferentiableAt ℝ (fun (r' : ℝ³) => (r' i - R i) ^ 2) r := by
    have h := (π[i]).hasFDerivAt (x := r)
    exact ((h.sub_const (R i)).pow 2).differentiableAt
  have hsum : fderiv ℝ (fun (r' : ℝ³) => ∑ i : Fin 3, (r' i - R i) ^ 2) r =
      ∑ i : Fin 3, (2 * (r i - R i)) • π[i] := by
    have := fderiv_sum (fun (i : Fin 3) (_hi : i ∈ (Finset.univ : Finset (Fin 3))) => h_sq_diff i)
    -- this : fderiv ℝ (∑ i ∈ Finset.univ, (fun r' => (r' i - R i) ^ 2)) r =
    --   ∑ i ∈ Finset.univ, fderiv ℝ (fun r' => (r' i - R i) ^ 2) r
    simpa [Finset.sum_apply, h_sq] using this
  have hsum_diff : DifferentiableAt ℝ (fun (r' : ℝ³) => ∑ i : Fin 3, (r' i - R i) ^ 2) r := by
    simpa [Finset.sum_apply] using
      DifferentiableAt.sum (fun (i : Fin 3) (_hi : i ∈ (Finset.univ : Finset (Fin 3))) => h_sq_diff i)
  have hg_diff : DifferentiableAt ℝ (fun r' : ℝ³ => -α * ∑ i : Fin 3, (r' i - R i) ^ 2) r :=
    hsum_diff.const_mul (-α)
  unfold primitiveGTO_s primitiveGTO
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
  rw [fderiv_exp hg_diff]
  congr 1
  rw [fderiv_const_mul hsum_diff (-α), hsum]
  simp [smul_smul, Finset.smul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The directional derivative of `primitiveGTO_s α R` along coordinate `i`. -/
lemma deriv_coord_primitiveGTO_s (α : ℝ) (R : ℝ³) (i : Fin 3) (r : ℝ³) :
    (fderiv ℝ (primitiveGTO_s α R) r) (Pi.single i (1 : ℝ)) =
      (-2 * α) * (r i - R i) * (primitiveGTO_s α R r) := by
  rw [fderiv_primitiveGTO_s α R r]
  calc
    ((primitiveGTO_s α R r) • (∑ j : Fin 3, ((-2 * α) * (r j - R j)) • π[j]))
        (Pi.single i (1 : ℝ))
    = (primitiveGTO_s α R r) * ((∑ j : Fin 3, ((-2 * α) * (r j - R j)) • π[j])
        (Pi.single i (1 : ℝ))) := by simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = (primitiveGTO_s α R r) * ((-2 * α) * (r i - R i)) := by rw [proj_sum_apply_single]
    _ = (-2 * α) * (r i - R i) * (primitiveGTO_s α R r) := by ring

/-! ## 3D Gaussian integral lemmas -/

/-- The 3D Gaussian integral ∫ exp(-γ·|r|²) dr = (√(π/γ))³, for γ > 0. -/
lemma integral_exp_neg_mul_sq_sum_3d (γ : ℝ) (hγ : 0 < γ) :
    (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) = (Real.sqrt (π / γ)) ^ 3 := by
  calc
    (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2))
    _ = (∫ r : ℝ³, ∏ i : Fin 3, Real.exp (-γ * (r i) ^ 2)) := by
      refine integral_congr_ae ?_
      filter_upwards with r
      rw [Finset.mul_sum, ← Real.exp_sum]
    _ = (∫ x : ℝ, Real.exp (-γ * x ^ 2)) ^ 3 := by
      rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-γ * x ^ 2))]
      simp [Fintype.card_fin]
    _ = (Real.sqrt (π / γ)) ^ 3 := by rw [integral_gaussian]

/-- ∫ r_i²·exp(-γ·Σ_j r_j²) dr = (∫ x²·exp(-γx²) dx)·(∫ exp(-γx²) dx)². -/
lemma integral_coord_sq_exp_neg_mul_sq_sum_3d (γ : ℝ) (hγ : 0 < γ) (i : Fin 3) :
    (∫ r : ℝ³, (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) =
      (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) *
        ((∫ x : ℝ, Real.exp (-γ * x ^ 2)) ^ 2) := by
  -- Convert ∑ j, r_j² = r₀²+r₁²+r₂² and expand
  have h_exp_sum (r : ℝ³) : Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
      Real.exp (-γ * (r 0) ^ 2) * Real.exp (-γ * (r 1) ^ 2) * Real.exp (-γ * (r 2) ^ 2) := by
    rw [Finset.mul_sum, Fin.sum_univ_three, Real.exp_add, Real.exp_add]
  let g : Fin 3 → ℝ → ℝ := fun j =>
    if j = i then (fun x => x ^ 2 * Real.exp (-γ * x ^ 2))
    else (fun x => Real.exp (-γ * x ^ 2))
  have h_factor (r : ℝ³) : (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
      ∏ j : Fin 3, g j (r j) := by
    rw [h_exp_sum r, Fin.prod_univ_three]
    dsimp [g]
    -- Now: (r i)^2 * exp₀*exp₁*exp₂ = g₀(r₀)*g₁(r₁)*g₂(r₂)
    -- Case analysis on i via fin_cases
    fin_cases i <;> {simp; ring}
  calc
    (∫ r : ℝ³, (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2))
    _ = (∫ r : ℝ³, ∏ j : Fin 3, g j (r j)) :=
      integral_congr_ae (by filter_upwards with r; rw [h_factor r])
    _ = ∏ j : Fin 3, (∫ x : ℝ, g j x) := integral_fintype_prod_volume_eq_prod g
    _ = ((∫ x : ℝ, g 0 x) * (∫ x : ℝ, g 1 x) * (∫ x : ℝ, g 2 x)) := by rw [Fin.prod_univ_three]
    _ = (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) *
        ((∫ x : ℝ, Real.exp (-γ * x ^ 2)) ^ 2) := by
      fin_cases i <;> {simp [g]; ring}

/-- Integrability of r_i²·exp(-γ·Σ_j r_j²) on ℝ³ (factors into product of 1D Gaussians). -/
lemma integrable_coord_sq_exp_neg_mul_sq_sum (γ : ℝ) (hγ : 0 < γ) (i : Fin 3) :
    Integrable (fun r : ℝ³ => (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) volume := by
  let g : Fin 3 → ℝ → ℝ := fun j =>
    if j = i then (fun x => x ^ 2 * Real.exp (-γ * x ^ 2))
    else (fun x => Real.exp (-γ * x ^ 2))
  have h_int_g (j : Fin 3) : Integrable (g j) volume := by
    dsimp [g]; split
    · have hk : (-1 : ℝ) < (2 : ℝ) := by norm_num
      have h := integrable_rpow_mul_exp_neg_mul_sq hγ hk
      simpa [Real.rpow_natCast] using h
    · exact integrable_exp_neg_mul_sq hγ
  have h_factor (r : ℝ³) : (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
      ∏ j : Fin 3, g j (r j) := by
    have h_exp_sum : Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
        Real.exp (-γ * (r 0) ^ 2) * Real.exp (-γ * (r 1) ^ 2) * Real.exp (-γ * (r 2) ^ 2) := by
      rw [Fin.sum_univ_three, mul_add, Real.exp_add, mul_add, Real.exp_add]
    rw [h_exp_sum, Fin.prod_univ_three]
    dsimp [g]
    fin_cases i <;> simp <;> ring
  conv =>
    arg 1; intro r
    rw [h_factor]
  exact MeasureTheory.Integrable.fintype_prod h_int_g

/-! ## Kinetic energy integral for s-type GTOs -/

/-- The kinetic energy integral for two same-center s-type primitive GTOs:
  `T = (αβ/(α+β)) · 3 · (√(π/(α+β)))³`.

Equivalently `T = (αβ/(α+β)) · 3 · S` where `S` is the same-center overlap; the factor `3`
counts the three spatial degrees of freedom. Requires `0 < α`, `0 < β`. -/
theorem kinetic_primitiveGTO_s_same_center (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (R : ℝ³) :
    kinetic (primitiveGTO_s α R) (primitiveGTO_s β R) =
      (α * β / (α + β)) * 3 * (Real.sqrt (π / (α + β))) ^ 3 := by
  have hγpos : α + β > 0 := by linarith
  set γ := α + β with hγ
  unfold kinetic
  -- Compute the gradient dot product ∇φ·∇ψ = Σᵢ ∂ᵢφ·∂ᵢψ
  -- ∂ᵢφ = -2α·(rᵢ-Rᵢ)·φ(r),  ∂ᵢψ = -2β·(rᵢ-Rᵢ)·ψ(r)
  -- So ∇φ·∇ψ = 4αβ·|r-R|²·exp(-γ·|r-R|²)
  have h_grad_dot (r : ℝ³) : (∑ i : Fin 3,
      (fderiv ℝ (primitiveGTO_s α R) r (Pi.single i 1)) *
      (fderiv ℝ (primitiveGTO_s β R) r (Pi.single i 1))) =
      4 * α * β * (∑ i : Fin 3, (r i - R i) ^ 2) *
        Real.exp (-γ * ∑ i : Fin 3, (r i - R i) ^ 2) := by
    have h_deriv (a : ℝ) (r' : ℝ³) (i : Fin 3) :
        (fderiv ℝ (primitiveGTO_s a R) r') (Pi.single i (1 : ℝ)) =
        (-2 * a) * (r' i - R i) * Real.exp (-a * ∑ j : Fin 3, (r' j - R j) ^ 2) := by
      rw [deriv_coord_primitiveGTO_s a R i r']
      simp [primitiveGTO_s, primitiveGTO, pow_zero, Finset.prod_const_one, one_mul]
    simp_rw [h_deriv α r, h_deriv β r]
    conv_lhs =>
      conv =>
        arg 2; intro i
        equals 4 * α * β * rexp (- γ * ∑ j, (r j - R j) ^ 2) * (r i - R i) ^ 2 =>
          rw [hγ, neg_add, add_mul, Real.exp_add]
          ring
      rw [← Finset.mul_sum]
    ring
  rw [integral_congr_ae (by filter_upwards with r; rw [h_grad_dot r])]
  -- Pull out constant factor 4αβ
  have h_factor : (fun r : ℝ³ => 4 * α * β * (∑ i : Fin 3, (r i - R i) ^ 2) *
      Real.exp (-γ * ∑ i : Fin 3, (r i - R i) ^ 2)) =
      (fun r : ℝ³ => (4 * α * β) * ((∑ i : Fin 3, (r i - R i) ^ 2) *
        Real.exp (-γ * ∑ i : Fin 3, (r i - R i) ^ 2))) := by
    ext r; ring
  rw [h_factor, integral_const_mul (4 * α * β)]
  -- Translate r ↦ r + R
  have h_trans : (∫ r : ℝ³, (∑ i : Fin 3, (r i - R i) ^ 2) *
      Real.exp (-γ * ∑ i : Fin 3, (r i - R i) ^ 2)) =
      (∫ r : ℝ³, (∑ i : Fin 3, (r i) ^ 2) * Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r : ℝ³ => (∑ i : Fin 3, (r i) ^ 2) * Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) R
    simpa [Pi.sub_apply] using h
  rw [h_trans]
  -- |r|² = Σᵢ rᵢ², split into sum of 3 coordinate integrals
  --rw [show (fun r : ℝ³ => (∑ i : Fin 3, (r i) ^ 2) * Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) =
  --    (fun r : ℝ³ => ∑ i : Fin 3, (r i) ^ 2 * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) by
  --  ext r; ring]
  conv_lhs =>
    arg 2; arg 2
    conv =>
      arg 2; intro x
      rw [Finset.sum_mul]
    rw [integral_finset_sum _ (fun i _ => integrable_coord_sq_exp_neg_mul_sq_sum γ hγpos i)]
  simp_rw [integral_coord_sq_exp_neg_mul_sq_sum_3d γ hγpos]
  simp only [one_div, neg_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  -- Now: (1/2)·4αβ · 3 · (∫ x²·exp(-γx²)) · (∫ exp(-γx²))²
  have hI0 : (∫ x : ℝ, Real.exp (-γ * x ^ 2)) = Real.sqrt (π / γ) := integral_gaussian γ
  have hI2 : (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) = (Real.sqrt (π / γ)) / (2 * γ) := by
    rw [integral_gaussian_moment_1d 2 γ hγpos]
    simp [gaussianMoment, show (2 : ℕ) % 2 = 0 by decide, show (2 : ℕ) / 2 = 1 by decide]
  conv_lhs at hI0 =>
    arg 2; intro x
    rw [neg_mul]
  conv_lhs at hI2 =>
    arg 2; intro x
    rw [neg_mul]
  rw [hI2, hI0]
  -- = (αβ/(α+β)) · 3 · (√(π/(α+β)))³
  have h_sq_sqrt : (Real.sqrt (π / γ)) ^ 2 = π / γ :=
    Real.sq_sqrt (div_nonneg (by positivity) (by linarith))
  field_simp [hγpos.ne.symm]
  ring


/-- The kinetic energy integral for two different-center s-type primitive GTOs:
  `T = (αβ/(α+β)) · (3 - 2αβ/(α+β) · ‖R₁-R₂‖²) · S(R₁,R₂)`,
where `S(R₁,R₂)` is the corresponding overlap. -/
theorem kinetic_primitiveGTO_s_diff_center (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (R₁ R₂ : ℝ³) :
    kinetic (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) =
      (α * β / (α + β)) *
        (3 - 2 * α * β / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        overlap (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) := by
  have hγpos : α + β > 0 := by linarith
  have hγne0 : α + β ≠ 0 := by linarith
  set γ := α + β with hγ
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / γ with hP
  set Δ := fun i : Fin 3 => R₁ i - R₂ i with hΔ
  unfold kinetic
  -- directional derivative formula for primitiveGTO_s
  have h_deriv (a : ℝ) (R' : ℝ³) (r' : ℝ³) (i : Fin 3) :
      (fderiv ℝ (primitiveGTO_s a R') r') (Pi.single i (1 : ℝ)) =
      (-2 * a) * (r' i - R' i) * Real.exp (-a * ∑ j : Fin 3, (r' j - R' j) ^ 2) := by
    rw [deriv_coord_primitiveGTO_s a R' i r']
    simp [primitiveGTO_s, primitiveGTO, pow_zero, Finset.prod_const_one, one_mul]
  -- gradient dot product ∇φ·∇ψ for different centers
  have h_grad_dot (r : ℝ³) : (∑ i : Fin 3,
      (fderiv ℝ (primitiveGTO_s α R₁) r (Pi.single i 1)) *
      (fderiv ℝ (primitiveGTO_s β R₂) r (Pi.single i 1))) =
      4 * α * β * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
        Real.exp (-α * ∑ j : Fin 3, (r j - R₁ j) ^ 2) *
        Real.exp (-β * ∑ j : Fin 3, (r j - R₂ j) ^ 2) := by
    simp_rw [h_deriv α R₁ r, h_deriv β R₂ r]
    set E₁ := Real.exp (-α * ∑ j : Fin 3, (r j - R₁ j) ^ 2) with hE₁
    set E₂ := Real.exp (-β * ∑ j : Fin 3, (r j - R₂ j) ^ 2) with hE₂
    calc
      (∑ i : Fin 3, ((-2 * α) * (r i - R₁ i) * E₁) * ((-2 * β) * (r i - R₂ i) * E₂))
      = (∑ i : Fin 3, (4 * α * β) * ((r i - R₁ i) * (r i - R₂ i)) * E₁ * E₂) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i : Fin 3, (4 * α * β * E₁ * E₂) * ((r i - R₁ i) * (r i - R₂ i))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (4 * α * β * E₁ * E₂) * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) := by
        rw [← Finset.mul_sum]
      _ = 4 * α * β * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) * E₁ * E₂ := by ring
  -- 1D completing-the-square identity
  have hsq (x a b : ℝ) : -α * (x - a) ^ 2 + -β * (x - b) ^ 2 =
      -(α * β) / γ * (a - b) ^ 2 + -γ * (x - (α * a + β * b) / γ) ^ 2 := by
    field_simp [hγne0]
    ring
  -- 3D exponential product = prefactor · translated Gaussian
  have h_exp_sum_eq (r : ℝ³) : Real.exp (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) *
      Real.exp (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2) =
      Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
      Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      (-α * ∑ i : Fin 3, (r i - R₁ i) ^ 2) + (-β * ∑ i : Fin 3, (r i - R₂ i) ^ 2) =
        ∑ i : Fin 3, (-α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α * β) / γ * (R₁ i - R₂ i) ^ 2 + -γ * (r i - P i) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        dsimp [P]
        rw [hsq (r i) (R₁ i) (R₂ i)]
      _ = (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) +
          (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  -- combine gradient dot product with exponent combining
  have h_integrand (r : ℝ³) :
      (∑ i : Fin 3, (fderiv ℝ (primitiveGTO_s α R₁) r (Pi.single i 1)) *
        (fderiv ℝ (primitiveGTO_s β R₂) r (Pi.single i 1))) =
      4 * α * β * Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        ((∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
          Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2)) := by
    rw [h_grad_dot r]
    calc
      4 * α * β * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
        Real.exp (-α * ∑ j : Fin 3, (r j - R₁ j) ^ 2) *
        Real.exp (-β * ∑ j : Fin 3, (r j - R₂ j) ^ 2)
      = 4 * α * β * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
          (Real.exp (-α * ∑ j : Fin 3, (r j - R₁ j) ^ 2) *
           Real.exp (-β * ∑ j : Fin 3, (r j - R₂ j) ^ 2)) := by ring
      _ = 4 * α * β * (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
          (Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
           Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2)) := by rw [h_exp_sum_eq r]
      _ = 4 * α * β * Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          ((∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
           Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2)) := by ring
  rw [integral_congr_ae (by filter_upwards with r; rw [h_integrand r])]
  -- pull out constant factor 4αβ·exp(...)
  set C := Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) with hC
  have h_factor : (fun r : ℝ³ => 4 * α * β * C *
      ((∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
        Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2))) =
      (fun r => (4 * α * β * C) * (((∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
        Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2)))) := by
    ext r; ring
  rw [h_factor, integral_const_mul (4 * α * β * C)]
  -- translate r ↦ r + P
  have h_trans : (∫ r : ℝ³, (∑ i : Fin 3, (r i - R₁ i) * (r i - R₂ i)) *
      Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2)) =
      (∫ r : ℝ³, (∑ i : Fin 3, (r i + P i - R₁ i) * (r i + P i - R₂ i)) *
        Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r : ℝ³ => (∑ i : Fin 3, (r i + P i - R₁ i) * (r i + P i - R₂ i)) *
        Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2)) P
    simpa [Pi.sub_apply, sub_add_cancel] using h
  rw [h_trans]
  -- integrability lemma for (rᵢ + A)(rᵢ + B)·exp(-γ|r|²)
  have h_int_term (i : Fin 3) (A B : ℝ) : Integrable
      (fun r : ℝ³ => (r i + A) * (r i + B) *
        Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) volume := by
    let g : Fin 3 → ℝ → ℝ := fun j =>
      if j = i then (fun x => (x + A) * (x + B) * Real.exp (-γ * x ^ 2))
      else (fun x => Real.exp (-γ * x ^ 2))
    have h_int_g (j : Fin 3) : Integrable (g j) volume := by
      dsimp [g]; split
      · -- (x+A)(x+B)·exp(-γx²) = x²·exp + (A+B)x·exp + AB·exp, a sum of integrable functions
        have h_sq : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-γ * x ^ 2)) volume := by
          have hk : (-1 : ℝ) < (2 : ℝ) := by norm_num
          have h := integrable_rpow_mul_exp_neg_mul_sq hγpos hk
          simpa [Real.rpow_natCast] using h
        have h_lin : Integrable (fun x : ℝ => x * Real.exp (-γ * x ^ 2)) volume := by
          have hk : (-1 : ℝ) < (1 : ℝ) := by norm_num
          have h := integrable_rpow_mul_exp_neg_mul_sq hγpos hk
          simpa [Real.rpow_natCast] using h
        have h_exp_g : Integrable (fun x : ℝ => Real.exp (-γ * x ^ 2)) volume :=
          integrable_exp_neg_mul_sq hγpos
        have h_eq : (fun x : ℝ => (x + A) * (x + B) * Real.exp (-γ * x ^ 2)) =
            (fun x => (x ^ 2 * Real.exp (-γ * x ^ 2)) +
              ((A + B) * (x * Real.exp (-γ * x ^ 2))) +
              (A * B * Real.exp (-γ * x ^ 2))) := by
          ext x; ring
        rw [h_eq]
        exact ((h_sq.add (h_lin.const_mul (A + B))).add (h_exp_g.const_mul (A * B)))
      · exact integrable_exp_neg_mul_sq hγpos
    have h_factor (r : ℝ³) : (r i + A) * (r i + B) *
        Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) = ∏ j : Fin 3, g j (r j) := by
      have h_exp_sum : Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
          Real.exp (-γ * (r 0) ^ 2) * Real.exp (-γ * (r 1) ^ 2) *
          Real.exp (-γ * (r 2) ^ 2) := by
        rw [Fin.sum_univ_three, mul_add, Real.exp_add, mul_add, Real.exp_add]
      rw [h_exp_sum, Fin.prod_univ_three]
      dsimp [g]
      fin_cases i <;> simp <;> ring
    conv =>
      arg 1; intro r
      rw [h_factor r]
    exact MeasureTheory.Integrable.fintype_prod h_int_g
  -- rewrite sum * exp as sum of products, then split integral
  -- adjust associativity: (r i + P i - R₁ i) → (r i + (P i - R₁ i))
  have h_integrand_assoc (r : ℝ³) :
      (∑ i : Fin 3, (r i + P i - R₁ i) * (r i + P i - R₂ i)) *
      Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
      ∑ i : Fin 3, ((r i + (P i - R₁ i)) * (r i + (P i - R₂ i)) *
        Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) := by
    simp [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  conv_lhs =>
    arg 2; arg 2
    rw [integral_congr_ae (by filter_upwards with r; rw [h_integrand_assoc r])]
    rw [integral_finset_sum _ (fun i _ => h_int_term i (P i - R₁ i) (P i - R₂ i))]
  -- integral value lemma for (rᵢ + A)(rᵢ + B)·exp(-γ|r|²)
  have h_int_val (i : Fin 3) (A B : ℝ) :
      (∫ r : ℝ³, (r i + A) * (r i + B) * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2)) =
      ((∫ x : ℝ, (x + A) * (x + B) * Real.exp (-γ * x ^ 2)) *
        ((∫ x : ℝ, Real.exp (-γ * x ^ 2)) ^ 2)) := by
    let g : Fin 3 → ℝ → ℝ := fun j =>
      if j = i then (fun x => (x + A) * (x + B) * Real.exp (-γ * x ^ 2))
      else (fun x => Real.exp (-γ * x ^ 2))
    have h_factor (r : ℝ³) : (r i + A) * (r i + B) *
        Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) = ∏ j : Fin 3, g j (r j) := by
      have h_exp_sum : Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2) =
          Real.exp (-γ * (r 0) ^ 2) * Real.exp (-γ * (r 1) ^ 2) *
          Real.exp (-γ * (r 2) ^ 2) := by
        rw [Fin.sum_univ_three, mul_add, Real.exp_add, mul_add, Real.exp_add]
      rw [h_exp_sum, Fin.prod_univ_three]
      dsimp [g]
      fin_cases i <;> simp <;> ring
    calc
      (∫ r : ℝ³, (r i + A) * (r i + B) * Real.exp (-γ * ∑ j : Fin 3, (r j) ^ 2))
      = (∫ r : ℝ³, ∏ j : Fin 3, g j (r j)) :=
        integral_congr_ae (by filter_upwards with r; rw [h_factor r])
      _ = ∏ j : Fin 3, (∫ x : ℝ, g j x) := integral_fintype_prod_volume_eq_prod g
      _ = ((∫ x : ℝ, g 0 x) * (∫ x : ℝ, g 1 x) * (∫ x : ℝ, g 2 x)) := by
        rw [Fin.prod_univ_three]
      _ = ((∫ x : ℝ, (x + A) * (x + B) * Real.exp (-γ * x ^ 2)) *
          ((∫ x : ℝ, Real.exp (-γ * x ^ 2)) ^ 2)) := by
        fin_cases i <;> simp [g] <;> ring
  -- apply the integral value lemma for each coordinate
  simp_rw [h_int_val]
  -- 1D Gaussian moment results
  have h_int_xk (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (-γ * x ^ 2)) volume := by
    have hk : (-1 : ℝ) < (k : ℝ) := by
      have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq hγpos hk
    simpa [Real.rpow_natCast] using h
  have hi_exp : Integrable (fun x : ℝ => Real.exp (-γ * x ^ 2)) volume := by
    simpa using h_int_xk 0
  have hi_lin : Integrable (fun x : ℝ => x * Real.exp (-γ * x ^ 2)) volume := by
    simpa using h_int_xk 1
  have hi_sq : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-γ * x ^ 2)) volume :=
    h_int_xk 2
  have hI0 : (∫ x : ℝ, Real.exp (-γ * x ^ 2)) = Real.sqrt (π / γ) := by
    simpa [neg_mul] using integral_gaussian γ
  have hI1 : (∫ x : ℝ, x * Real.exp (-γ * x ^ 2)) = 0 := by
    have h := integral_gaussian_moment_1d 1 γ hγpos
    simpa [gaussianMoment] using h
  have hI2 : (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) = Real.sqrt (π / γ) / (2 * γ) := by
    have h := integral_gaussian_moment_1d 2 γ hγpos
    simpa [gaussianMoment, show (2 : ℕ) % 2 = 0 by decide, show (2 : ℕ) / 2 = 1 by decide] using h
  -- for any A B: ∫ (x+A)(x+B)·exp(-γx²) = I₂ + AB·I₀ (linear term vanishes by I₁=0)
  have h_prod_1d (A B : ℝ) : (∫ x : ℝ, (x + A) * (x + B) * Real.exp (-γ * x ^ 2)) =
      (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) +
        A * B * (∫ x : ℝ, Real.exp (-γ * x ^ 2)) := by
    set f : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-γ * x ^ 2) with hf
    set g : ℝ → ℝ := fun x => (A + B) * (x * Real.exp (-γ * x ^ 2)) with hg
    set h : ℝ → ℝ := fun x => A * B * Real.exp (-γ * x ^ 2) with hh
    have hif : Integrable f volume := hi_sq
    have hig : Integrable g volume := hi_lin.const_mul (A + B)
    have hih : Integrable h volume := hi_exp.const_mul (A * B)
    have h_expand (x : ℝ) : (x + A) * (x + B) * Real.exp (-γ * x ^ 2) = f x + g x + h x := by
      dsimp [f, g, h]; ring
    calc
      (∫ x : ℝ, (x + A) * (x + B) * Real.exp (-γ * x ^ 2))
      = (∫ x : ℝ, f x + g x + h x) :=
        integral_congr_ae (by filter_upwards with x; rw [h_expand x])
      _ = (∫ x : ℝ, f x + (g x + h x)) :=
        integral_congr_ae (by filter_upwards with x; ring)
      _ = (∫ x : ℝ, f x) + (∫ x : ℝ, g x + h x) :=
        integral_add hif (hig.add hih)
      _ = (∫ x : ℝ, f x) + ((∫ x : ℝ, g x) + (∫ x : ℝ, h x)) := by
        rw [integral_add hig hih]
      _ = (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) +
          ((A + B) * (∫ x : ℝ, x * Real.exp (-γ * x ^ 2)) +
           A * B * (∫ x : ℝ, Real.exp (-γ * x ^ 2))) := by
        simp [f, g, h, integral_const_mul]
      _ = (∫ x : ℝ, x ^ 2 * Real.exp (-γ * x ^ 2)) +
          A * B * (∫ x : ℝ, Real.exp (-γ * x ^ 2)) := by rw [hI1]; ring
  -- apply to each coordinate: Aᵢ = Pᵢ-R₁ᵢ, Bᵢ = Pᵢ-R₂ᵢ
  have hA (i : Fin 3) : P i - R₁ i = -(β * Δ i) / γ := by
    dsimp [P, Δ]; field_simp [hγne0]; ring
  have hB (i : Fin 3) : P i - R₂ i = (α * Δ i) / γ := by
    dsimp [P, Δ]; field_simp [hγne0]; ring
  have hAB (i : Fin 3) : (P i - R₁ i) * (P i - R₂ i) = -(α * β) * (Δ i) ^ 2 / γ ^ 2 := by
    rw [hA i, hB i]; field_simp [hγne0]
  simp_rw [h_prod_1d (P _ - R₁ _) (P _ - R₂ _)]
  simp_rw [hAB]
  simp_rw [hI2, hI0]
  -- goal: 1/2 * 4αβ*C * Σᵢ [(√(π/γ)/(2γ) - αβ·Δᵢ²·√(π/γ)/γ²) * (√(π/γ))²] = target
  set S := Real.sqrt (π / γ) with hS
  have hSsq : S ^ 2 = π / γ :=
    Real.sq_sqrt (div_nonneg (by positivity) (by linarith [hγpos]))
  have h_sum_Δ_sq : (∑ i : Fin 3, (Δ i) ^ 2) = ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2 := by simp [Δ]
  have h_overlap : overlap (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) = S ^ 3 * C := by
    rw [overlap_primitiveGTO_s_diff_center α β hγne0 R₁ R₂, ← hγ, hS, hC]
  have h_sum_calc : (∑ x : Fin 3, (S ^ 3 / (2 * γ) - (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2)) =
      S ^ 3 * (3 / (2 * γ) - (α * β / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2)) := by
    have h_s1 : (∑ x : Fin 3, S ^ 3 / (2 * γ)) = 3 * (S ^ 3 / (2 * γ)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_s2 : (∑ x : Fin 3, (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2) =
        (α * β * S ^ 3 / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2) := by
      calc
        (∑ x : Fin 3, (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2)
        = (∑ x : Fin 3, (α * β * S ^ 3 / γ ^ 2) * (Δ x) ^ 2) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          ring
        _ = (α * β * S ^ 3 / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2) := by
          rw [← Finset.mul_sum]
    calc
      (∑ x : Fin 3, (S ^ 3 / (2 * γ) - (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2))
      = (∑ x : Fin 3, S ^ 3 / (2 * γ)) -
          (∑ x : Fin 3, (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2) := by
        rw [Finset.sum_sub_distrib]
      _ = 3 * (S ^ 3 / (2 * γ)) -
          (α * β * S ^ 3 / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2) := by rw [h_s1, h_s2]
      _ = S ^ 3 * (3 / (2 * γ) - (α * β / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2)) := by ring
  calc
    1 / 2 * (4 * α * β * C * ∑ x : Fin 3, (S / (2 * γ) + -(α * β) * (Δ x) ^ 2 / γ ^ 2 * S) * S ^ 2)
    = 2 * α * β * C * (∑ x : Fin 3, (S / (2 * γ) + -(α * β) * (Δ x) ^ 2 / γ ^ 2 * S) * S ^ 2) := by ring
    _ = 2 * α * β * C * (∑ x : Fin 3, (S ^ 3 / (2 * γ) - (α * β) * (Δ x) ^ 2 * S ^ 3 / γ ^ 2)) := by
      refine congrArg _ (Finset.sum_congr rfl (fun x _ => ?_))
      ring
    _ = 2 * α * β * C * S ^ 3 *
        (3 / (2 * γ) - (α * β / γ ^ 2) * (∑ x : Fin 3, (Δ x) ^ 2)) := by rw [h_sum_calc]; ring
    _ = (α * β / γ) * C * S ^ 3 *
        (3 - 2 * α * β / γ * (∑ x : Fin 3, (Δ x) ^ 2)) := by
      field_simp [hγpos.ne.symm]
    _ = (α * β / γ) * (3 - 2 * α * β / γ * (∑ x : Fin 3, (R₁ x - R₂ x) ^ 2)) *
        (C * S ^ 3) := by rw [h_sum_Δ_sq]; ring
    _ = (α * β / γ) * (3 - 2 * α * β / γ * (∑ x : Fin 3, (R₁ x - R₂ x) ^ 2)) *
        overlap (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) := by rw [h_overlap]; ring
    _ = (α * β / (α + β)) *
        (3 - 2 * α * β / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        overlap (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) := by simp [hγ]

end GTO
