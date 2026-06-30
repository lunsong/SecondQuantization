import SecondQuantization.GTO.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coulomb integrals and the Boys function

This file derives the closed forms of the s-type **nuclear-attraction** and
**electron-repulsion** (two-electron, ERI) integrals, expressing each in terms of the Boys
function `boys0 t = ∫₀¹ exp(-t u²) du`.

The route is the standard one. The Coulomb kernel `1/‖r - A‖` is rewritten almost-everywhere as
a Gaussian integral `1/‖r-A‖ = (2/√π) ∫_{Ioi 0} exp(-‖r-A‖² t²) dt` (section 6). Swapping this
against a Gaussian — justified by Tonelli/Fubini on a nonnegative integrand (section 8) — and
evaluating the resulting 3D Gaussian product integral (section 5) leaves a 1D integral that the
change of variables `u = t/√(γ+t²)`, mapping `(0,∞)` onto `(0,1)`, reduces exactly to `boys0`
(section 7). The nuclear-attraction result (section 9) is one such swap; the ERI (section 11) is
two nested swaps, with a second change of variables (section 10) handling the inner one.

## Main results

* `nuclearAttraction_primitiveGTO_s` — closed form of the one-electron nuclear attraction.
* `electronRepulsion_primitiveGTO_s` — closed form of the two-electron repulsion integral.
-/

namespace GTO

open Real MeasureTheory Set

set_option linter.style.longLine false

/-- The Boys function `boys0 t = ∫₀¹ exp(-t · u²) du`, the special function to which the
nuclear-attraction and electron-repulsion integrals reduce. This is the zeroth Boys function
`F₀(t)`; higher angular momenta would require `Fₖ(t) = ∫₀¹ u^(2k) exp(-t u²) du`. -/
noncomputable def boys0 (t : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-t * u ^ 2)

/-- The `n`-th Boys function `boys n t = ∫₀¹ u^(2n) · exp(-t·u²) du`, so `boys 0 = boys0`.
Higher angular momenta in the nuclear-attraction and electron-repulsion integrals reduce to
finite linear combinations of `boys n` (via the recurrences `boys_succ_*` and the auxiliary
moment recurrences `coulombMomentν_succ`, `eriMomentν_succ_*` below). -/
noncomputable def boys (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, u ^ (2 * n) * Real.exp (-t * u ^ 2)

/-- The zeroth Boys function is `boys0`. -/
lemma boys_eq_boys0 : boys 0 = boys0 := by sorry

/-- Value at the origin: `boys n 0 = 1/(2n+1)`. -/
lemma boys_zero_val (n : ℕ) : boys n 0 = 1 / (2 * (n : ℝ) + 1) := by sorry

/-- Vertical recurrence `boys (n+1) t = ((2n+1)·boys n t - exp(-t)) / (2t)` for `t ≠ 0`,
obtained by integrating `d(u^(2n+1)·exp(-t·u²))/du` over `[0,1]`. -/
lemma boys_succ (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    boys (n + 1) t = ((2 * (n : ℝ) + 1) * boys n t - Real.exp (-t)) / (2 * t) := by sorry

/-- The `n`-th `t`-derivative of `boys0` is `(-1)^n · boys n`, since differentiating under the
integral brings down a factor `(-u²)^n`. -/
lemma boys_iteratedDeriv (n : ℕ) (t : ℝ) :
    (deriv^[n] boys0) t = (-1 : ℝ) ^ n * boys n t := by sorry

/-! ## 1. Derivative of `u/√(γ+u²)` = `γ/(γ+u²)^(3/2)` -/

/-- Derivative of `x ↦ x / √(γ + x²)`: it is `γ / (γ + x²)^(3/2)`, which is positive for
`0 < γ`. This derivative is the Jacobian of the change of variables used in section 7. -/
lemma hasDerivAt_u_div_sqrt_add_sq (γ : ℝ) (hγ : 0 < γ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => x / Real.sqrt (γ + x ^ 2)) (γ / ((γ + u ^ 2) ^ (3/2 : ℝ))) u := by
  have h_add_pos : 0 < γ + u ^ 2 := by nlinarith
  have h_sqrt_ne : Real.sqrt (γ + u ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h_add_pos).ne'
  have h_sq_deriv : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    have h_mul := (hasDerivAt_id u).mul (hasDerivAt_id u)
    simpa [sq, two_mul] using h_mul
  have h_add_deriv : HasDerivAt (fun x : ℝ => γ + x ^ 2) (2 * u) u := h_sq_deriv.const_add γ
  have h_denom_deriv : HasDerivAt (fun x : ℝ => Real.sqrt (γ + x ^ 2)) (u / Real.sqrt (γ + u ^ 2)) u := by
    have h_sqrt_deriv : HasDerivAt Real.sqrt ((2 * Real.sqrt (γ + u ^ 2))⁻¹) (γ + u ^ 2) := by
      simpa [one_div] using hasDerivAt_sqrt (by nlinarith : γ + u ^ 2 ≠ 0)
    have h_comp := HasDerivAt.comp u h_sqrt_deriv h_add_deriv
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_comp
  have h_div := HasDerivAt.div (hasDerivAt_id u) h_denom_deriv h_sqrt_ne
  refine h_div.congr_deriv ?_
  field_simp [h_sqrt_ne, show γ + u ^ 2 ≠ 0 from by nlinarith]
  have h_sq_sqrt : Real.sqrt (γ + u ^ 2) ^ 2 = γ + u ^ 2 := Real.sq_sqrt (by nlinarith)
  rw [h_sq_sqrt]
  -- Goal: (γ + u² - u*u) * (γ+u²)^(3/2) = γ * √(γ+u²)³
  have h_simp : γ + u ^ 2 - u * u = γ := by ring
  calc
    (γ + u ^ 2 - u * u) * (γ + u ^ 2) ^ (3/2 : ℝ) = γ * (γ + u ^ 2) ^ (3/2 : ℝ) := by rw [h_simp]
    _ = γ * (Real.sqrt (γ + u ^ 2)) ^ 3 := by
      rcases eq_or_ne γ 0 with (rfl | hγ_ne)
      · simp
      · rw [← mul_left_inj' hγ_ne]
        have h_pow_eq : (γ + u ^ 2) ^ (3/2 : ℝ) = (Real.sqrt (γ + u ^ 2)) ^ 3 := by
          calc
            (γ + u ^ 2) ^ (3/2 : ℝ) = (γ + u ^ 2) ^ ((1/2 : ℝ) * (3 : ℝ)) := by norm_num
            _ = ((γ + u ^ 2) ^ (1/2 : ℝ)) ^ (3 : ℝ) := by
              rw [rpow_mul (by nlinarith : 0 ≤ γ + u ^ 2) (1/2 : ℝ) (3 : ℝ)]
            _ = (Real.sqrt (γ + u ^ 2)) ^ (3 : ℝ) := by rw [Real.sqrt_eq_rpow]
            _ = (Real.sqrt (γ + u ^ 2)) ^ 3 := by norm_num
        rw [h_pow_eq]

/-! ## 2. Strict monotonicity on (0,∞) -/

/-- `x ↦ x / √(γ + x²)` is strictly increasing on `(0, ∞)` (its derivative is positive), so it
is a valid change-of-variables map. -/
lemma strictMonoOn_u_div_sqrt_add_sq (γ : ℝ) (hγ : 0 < γ) :
    StrictMonoOn (fun x : ℝ => x / Real.sqrt (γ + x ^ 2)) (Ioi 0) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hsqrt_x_pos : 0 < Real.sqrt (γ + x ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hsqrt_y_pos : 0 < Real.sqrt (γ + y ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have h_cross_sq : (x * Real.sqrt (γ + y ^ 2)) ^ 2 < (y * Real.sqrt (γ + x ^ 2)) ^ 2 := by
    calc
      (x * Real.sqrt (γ + y ^ 2)) ^ 2 = x ^ 2 * (Real.sqrt (γ + y ^ 2)) ^ 2 := by ring
      _ = x ^ 2 * (γ + y ^ 2) := by rw [Real.sq_sqrt (show 0 ≤ γ + y ^ 2 from by nlinarith)]
      _ = x ^ 2 * γ + x ^ 2 * y ^ 2 := by ring
      _ < y ^ 2 * γ + x ^ 2 * y ^ 2 := by
        have h_sq : x ^ 2 < y ^ 2 := by nlinarith
        nlinarith
      _ = y ^ 2 * (γ + x ^ 2) := by ring
      _ = y ^ 2 * (Real.sqrt (γ + x ^ 2)) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ γ + x ^ 2 from by nlinarith)]
      _ = (y * Real.sqrt (γ + x ^ 2)) ^ 2 := by ring
  have h_nonneg_x : 0 ≤ x * Real.sqrt (γ + y ^ 2) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have h_nonneg_y : 0 ≤ y * Real.sqrt (γ + x ^ 2) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have h_cross : x * Real.sqrt (γ + y ^ 2) < y * Real.sqrt (γ + x ^ 2) := by
    have h_abs := (sq_lt_sq.mp h_cross_sq)
    rw [abs_of_nonneg h_nonneg_x, abs_of_nonneg h_nonneg_y] at h_abs
    exact h_abs
  set P := Real.sqrt (γ + x ^ 2) * Real.sqrt (γ + y ^ 2) with hP
  have hP_pos : 0 < P := mul_pos hsqrt_x_pos hsqrt_y_pos
  have h_invP_pos : 0 < P⁻¹ := inv_pos.mpr hP_pos
  have h_temp : (x * Real.sqrt (γ + y ^ 2)) / P < (y * Real.sqrt (γ + x ^ 2)) / P := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right h_cross h_invP_pos
  have h_simp_left : (x * Real.sqrt (γ + y ^ 2)) / P = x / Real.sqrt (γ + x ^ 2) := by
    dsimp [P]; field_simp [hsqrt_x_pos.ne', hsqrt_y_pos.ne']
  have h_simp_right : (y * Real.sqrt (γ + x ^ 2)) / P = y / Real.sqrt (γ + y ^ 2) := by
    dsimp [P]; field_simp [hsqrt_x_pos.ne', hsqrt_y_pos.ne']
  rw [h_simp_left, h_simp_right] at h_temp
  exact h_temp

/-! ## 3. Image of (0,∞) is (0,1) -/

/-- The map `x ↦ x / √(γ + x²)` sends `(0, ∞)` onto `(0, 1)`: the bound `x < √(γ + x²)` gives
the upper limit `< 1`, and `y ↦ y√γ/√(1-y²)` is an explicit inverse. -/
lemma image_Ioi_u_div_sqrt_add_sq (γ : ℝ) (hγ : 0 < γ) :
    (fun x : ℝ => x / Real.sqrt (γ + x ^ 2)) '' (Ioi (0 : ℝ)) = Ioo (0 : ℝ) 1 := by
  set f := fun x : ℝ => x / Real.sqrt (γ + x ^ 2) with hf
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_denom_pos : 0 < Real.sqrt (γ + x ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have h_lower : 0 < f x := by dsimp [f]; exact div_pos hx h_denom_pos
    have h_upper : f x < 1 := by
      dsimp [f]
      refine (div_lt_one ?_).mpr ?_
      · exact h_denom_pos
      · calc
          x = Real.sqrt (x ^ 2) := by rw [Real.sqrt_sq (hx.le)]
          _ < Real.sqrt (γ + x ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    exact ⟨h_lower, h_upper⟩
  · intro y hy
    rcases hy with ⟨hy_low, hy_high⟩
    set x := y * Real.sqrt γ / Real.sqrt (1 - y ^ 2) with hx_def
    have h_one_minus_y_sq_pos : 0 < 1 - y ^ 2 := by nlinarith
    have hx_pos : 0 < x := by
      refine div_pos (mul_pos hy_low (Real.sqrt_pos.mpr hγ)) (Real.sqrt_pos.mpr h_one_minus_y_sq_pos)
    have h_eq : f x = y := by
      dsimp [f, x]
      have h_sq_eq : ((y * Real.sqrt γ / Real.sqrt (1 - y ^ 2)) /
          Real.sqrt (γ + (y * Real.sqrt γ / Real.sqrt (1 - y ^ 2)) ^ 2)) ^ 2 = y ^ 2 := by
        set A := y * Real.sqrt γ / Real.sqrt (1 - y ^ 2) with hA
        have hA_sq : A ^ 2 = y ^ 2 * γ / (1 - y ^ 2) := by
          dsimp [A]
          calc
            (y * Real.sqrt γ / Real.sqrt (1 - y ^ 2)) ^ 2
                = (y * Real.sqrt γ) ^ 2 / (Real.sqrt (1 - y ^ 2)) ^ 2 := by ring
            _ = (y ^ 2 * ((Real.sqrt γ) ^ 2)) / (Real.sqrt (1 - y ^ 2)) ^ 2 := by ring
            _ = (y ^ 2 * γ) / (Real.sqrt (1 - y ^ 2)) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ γ from by linarith)]
            _ = (y ^ 2 * γ) / (1 - y ^ 2) := by rw [Real.sq_sqrt (show 0 ≤ 1 - y ^ 2 from by nlinarith)]
        have h_sum : γ + A ^ 2 = γ / (1 - y ^ 2) := by
          rw [hA_sq]
          field_simp [show 1 - y ^ 2 ≠ 0 from by nlinarith]
          ring
        calc
          (A / Real.sqrt (γ + A ^ 2)) ^ 2 = A ^ 2 / ((Real.sqrt (γ + A ^ 2)) ^ 2) := by ring
          _ = A ^ 2 / (γ + A ^ 2) := by rw [Real.sq_sqrt (show 0 ≤ γ + A ^ 2 from by nlinarith)]
          _ = (y ^ 2 * γ / (1 - y ^ 2)) / (γ + A ^ 2) := by rw [hA_sq]
          _ = (y ^ 2 * γ / (1 - y ^ 2)) / (γ / (1 - y ^ 2)) := by rw [h_sum]
          _ = y ^ 2 := by field_simp [show 1 - y ^ 2 ≠ 0 from by nlinarith]
      have h_nonneg_val : 0 ≤ (y * Real.sqrt γ / Real.sqrt (1 - y ^ 2)) /
          Real.sqrt (γ + (y * Real.sqrt γ / Real.sqrt (1 - y ^ 2)) ^ 2) := by
        refine div_nonneg ?_ (Real.sqrt_nonneg _)
        exact div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      have h_nonneg_y : 0 ≤ y := by linarith
      nlinarith
    exact ⟨x, hx_pos, h_eq⟩

/-! ## 4. Integral representation of `1/√s` -/

/-- Gaussian integral representation of the inverse square root:
  `1/√s = (2/√π) ∫_{Ioi 0} exp(-s t²) dt` for `0 < s`. Applied to `s = ‖r-A‖²`, this rewrites
the Coulomb kernel `1/‖r-A‖` as a Gaussian integral, enabling a Fubini swap against a Gaussian
basis function. -/
lemma one_div_sqrt_eq_integral_Ioi (s : ℝ) (hs : 0 < s) :
    1 / Real.sqrt s = (2 / Real.sqrt π) * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t ^ 2) := by
  rw [integral_gaussian_Ioi s]
  calc
    1 / Real.sqrt s = Real.sqrt 1 / Real.sqrt s := by simp
    _ = Real.sqrt (1 / s) := by rw [← Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)) s]
    _ = Real.sqrt ((π / s) / π) := by field_simp
    _ = Real.sqrt (π / s) / Real.sqrt π := by rw [Real.sqrt_div (by positivity) π]
    _ = (2 / Real.sqrt π) * (Real.sqrt (π / s) / 2) := by ring

/-! ## 5. 3D Gaussian product integral -/

/-- Product of two Gaussians as a single translated Gaussian (the 3D completing-the-square /
Gaussian-product identity):
  `∫ exp(-γ‖r‖² - t²‖r-A‖²) dr = (√(π/(γ+t²)))³ · exp(-γt²/(γ+t²) · ‖A‖²)`,
with product center `(t²·A)/(γ+t²)`. -/
lemma integral_exp_combined_3d (γ t : ℝ) (hγ : 0 < γ) (A : ℝ³) :
    (∫ r : ℝ³, Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2)) =
    (Real.sqrt (π / (γ + t ^ 2))) ^ 3 *
      Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * ∑ i : Fin 3, (A i) ^ 2) := by
  set p := γ + t ^ 2 with hp
  have hp_pos : 0 < p := by nlinarith
  have hp_ne_zero : p ≠ 0 := by nlinarith
  set P : ℝ³ := fun i => (t ^ 2 * A i) / p with hP
  have hsq : ∀ x a : ℝ,
      -γ * x ^ 2 + -(t ^ 2) * (x - a) ^ 2 = -(γ * t ^ 2) / p * a ^ 2 + -p * (x - (t ^ 2 * a) / p) ^ 2 := by
    intro x a; dsimp [p]; field_simp [hp_ne_zero]; ring
  have h_exp_sum_eq : ∀ r : ℝ³,
      -γ * ∑ i, (r i) ^ 2 + -(t ^ 2) * ∑ i, (r i - A i) ^ 2 =
        (-(γ * t ^ 2) / p * ∑ i, (A i) ^ 2) + (-p * ∑ i, (r i - P i) ^ 2) := by
    intro r
    have step : ∀ i : Fin 3,
        -γ * (r i) ^ 2 + -(t ^ 2) * (r i - A i) ^ 2 = -(γ * t ^ 2) / p * (A i) ^ 2 + -p * (r i - P i) ^ 2 := by
      intro i; rw [hP]; exact hsq (r i) (A i)
    calc
      -γ * ∑ i, (r i) ^ 2 + -(t ^ 2) * ∑ i, (r i - A i) ^ 2 = ∑ i, (-γ * (r i) ^ 2 + -(t ^ 2) * (r i - A i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i, (-(γ * t ^ 2) / p * (A i) ^ 2 + -p * (r i - P i) ^ 2) := Finset.sum_congr rfl (fun i _ => step i)
      _ = (-(γ * t ^ 2) / p * ∑ i, (A i) ^ 2) + (-p * ∑ i, (r i - P i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  have h_integrand : ∀ r : ℝ³,
      Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2) =
      Real.exp (-(γ * t ^ 2) / p * ∑ i, (A i) ^ 2) * Real.exp (-p * ∑ i, (r i - P i) ^ 2) := by
    intro r
    calc
      Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2) = Real.exp ((-γ * ∑ i, (r i) ^ 2) + (-(t ^ 2) * ∑ i, (r i - A i) ^ 2)) := by ring_nf
      _ = Real.exp ((-(γ * t ^ 2) / p * ∑ i, (A i) ^ 2) + (-p * ∑ i, (r i - P i) ^ 2)) := by rw [h_exp_sum_eq r]
      _ = Real.exp (-(γ * t ^ 2) / p * ∑ i, (A i) ^ 2) * Real.exp (-p * ∑ i, (r i - P i) ^ 2) := by rw [Real.exp_add]
  set C := Real.exp (-(γ * t ^ 2) / p * ∑ i : Fin 3, (A i) ^ 2) with hC
  calc
    (∫ r : ℝ³, Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2))
        = (∫ r : ℝ³, C * Real.exp (-p * ∑ i, (r i - P i) ^ 2)) := by
          refine integral_congr_ae ?_; filter_upwards with r; rw [h_integrand r, hC]
    _ = C * (∫ r : ℝ³, Real.exp (-p * ∑ i, (r i - P i) ^ 2)) := by rw [integral_const_mul]
    _ = C * (∫ r : ℝ³, Real.exp (-p * ∑ i, (r i) ^ 2)) := by
      have h_trans := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
        (fun r : ℝ³ => Real.exp (-p * ∑ i, (r i) ^ 2)) P
      rw [← h_trans]; simp [Pi.sub_apply]
    _ = C * (Real.sqrt (π / p)) ^ 3 := by
      have h_gauss : (∫ r : ℝ³, Real.exp (-p * ∑ i, (r i) ^ 2)) = (Real.sqrt (π / p)) ^ 3 := by
        calc
          (∫ r : ℝ³, Real.exp (-p * ∑ i, (r i) ^ 2)) = (∫ r : ℝ³, ∏ i, Real.exp (-p * (r i) ^ 2)) := by
            refine integral_congr_ae ?_; filter_upwards with r; rw [Finset.mul_sum, ← Real.exp_sum]
          _ = (∫ x : ℝ, Real.exp (-p * x ^ 2)) ^ 3 := by
            rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-p * x ^ 2))]
            simp [Fintype.card_fin]
          _ = (Real.sqrt (π / p)) ^ 3 := by rw [integral_gaussian p]
      rw [h_gauss]
    _ = (Real.sqrt (π / p)) ^ 3 * C := by ring
    _ = (Real.sqrt (π / (γ + t ^ 2))) ^ 3 * Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * ∑ i : Fin 3, (A i) ^ 2) := by rw [hC, hp]

/-! ## 6. Coulomb potential AE representation -/

/-- Almost-everywhere representation of the Coulomb kernel as a Gaussian integral:
  `1/‖r - A‖ = (2/√π) ∫_{Ioi 0} exp(-‖r-A‖² t²) dt`, valid away from the singular point `r = A`
(a null set). It is `one_div_sqrt_eq_integral_Ioi` applied to `s = ‖r-A‖²`. -/
lemma coulomb_eq_integral_ae (A : ℝ³) :
    (fun r => coulomb r A) =ᵐ[volume] fun r => (2 / Real.sqrt π) * ∫ t in Ioi (0 : ℝ), Real.exp (-(∑ i, (r i - A i) ^ 2) * t ^ 2) := by
  have h_ae_ne : ∀ᵐ r : (ℝ³), r ≠ A := by
    have h_null : volume ({A} : Set (ℝ³)) = 0 := measure_singleton A
    rw [ae_iff]; simp
  filter_upwards [h_ae_ne] with r hr
  dsimp [coulomb]
  have h_sq_pos : 0 < ∑ i : Fin 3, (r i - A i) ^ 2 := by
    by_contra! hle
    have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, (r i - A i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_sum_zero : ∑ i : Fin 3, (r i - A i) ^ 2 = 0 := by linarith
    have h_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _) |>.mp h_sum_zero
    have h_eq : ∀ i, r i = A i := by
      intro i; have hz := h_zero i (Finset.mem_univ i); nlinarith
    exact hr (funext h_eq)
  rw [one_div_sqrt_eq_integral_Ioi _ h_sq_pos]

/-! ## 7. Change of variables `u = t/√(γ+t²)` for the Boys-function integral -/

/-- The change of variables `u = t / √(γ + t²)`, which maps `Ioi 0` onto `Ioo 0 1`.
Applies to the 1D integral that results from the 3D Gaussian integration of the Coulomb identity:
`∫_{Ioi 0} (√(π/(γ+t²)))³ · exp(-γ·S·t²/(γ+t²)) dt = (√π)³/γ · boys₀(γ·S)`. -/
lemma integral_Ioi_gaussian_sqrt_to_boys0 (γ S : ℝ) (hγ : 0 < γ) :
    (∫ t in Ioi (0 : ℝ), ((Real.sqrt (π / (γ + t ^ 2))) ^ 3) *
      Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * S)) =
    ((Real.sqrt π) ^ 3 / γ) * boys0 (γ * S) := by
  set f := fun t : ℝ => t / Real.sqrt (γ + t ^ 2) with hf
  set f' := fun t : ℝ => γ / ((γ + t ^ 2) ^ (3/2 : ℝ)) with hf'
  have h_deriv (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivWithinAt f (f' x) (Ioi (0 : ℝ)) x := by
    dsimp [f, f']
    exact (hasDerivAt_u_div_sqrt_add_sq γ hγ x).hasDerivWithinAt
  have h_mono : MonotoneOn f (Ioi (0 : ℝ)) := by
    intro a ha b hb hle
    rcases lt_or_eq_of_le hle with (hlt | heq)
    · exact ((strictMonoOn_u_div_sqrt_add_sq γ hγ) ha hb hlt).le
    · rw [heq]
  have h_image : f '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := image_Ioi_u_div_sqrt_add_sq γ hγ
  set g := fun u : ℝ => ((Real.sqrt π) ^ 3 / γ) * Real.exp (-(γ * S) * u ^ 2) with hg
  -- Key algebraic identity: the integrand equals f'(t) * g(f(t))
  have h_eq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ((Real.sqrt (π / (γ + t ^ 2))) ^ 3) *
      Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * S) = f' t * g (f t) := by
    have hpos : 0 ≤ γ + t ^ 2 := by nlinarith
    -- (Real.sqrt (γ + t²))³ = (γ + t²)^(3/2)
    have h_sqrt_cube : (Real.sqrt (γ + t ^ 2)) ^ 3 = (γ + t ^ 2) ^ (3/2 : ℝ) := by
      calc
        (Real.sqrt (γ + t ^ 2)) ^ 3 = ((γ + t ^ 2) ^ (1/2 : ℝ)) ^ 3 := by rw [Real.sqrt_eq_rpow]
        _ = ((γ + t ^ 2) ^ (1/2 : ℝ)) ^ (3 : ℝ) := by norm_num
        _ = (γ + t ^ 2) ^ ((1/2 : ℝ) * (3 : ℝ)) := by rw [rpow_mul hpos (1/2 : ℝ) (3 : ℝ)]
        _ = (γ + t ^ 2) ^ (3/2 : ℝ) := by ring_nf
    -- (Real.sqrt (π/(γ+t²)))³ = (Real.sqrt π)³ / (γ+t²)^(3/2)
    have h_sqrt_pi_cube : (Real.sqrt (π / (γ + t ^ 2))) ^ 3 =
        ((Real.sqrt π) ^ 3) / ((γ + t ^ 2) ^ (3/2 : ℝ)) := by
      rw [Real.sqrt_div (by positivity : 0 ≤ π) _]
      calc
        ((Real.sqrt π) / Real.sqrt (γ + t ^ 2)) ^ 3 = (Real.sqrt π) ^ 3 / (Real.sqrt (γ + t ^ 2)) ^ 3 := by ring
        _ = (Real.sqrt π) ^ 3 / ((γ + t ^ 2) ^ (3/2 : ℝ)) := by rw [h_sqrt_cube]
    -- f(t)² = t²/(γ+t²)
    have h_sq : (f t) ^ 2 = t ^ 2 / (γ + t ^ 2) := by
      dsimp [f]
      calc
        (t / Real.sqrt (γ + t ^ 2)) ^ 2 = t ^ 2 / (Real.sqrt (γ + t ^ 2)) ^ 2 := by ring
        _ = t ^ 2 / (γ + t ^ 2) := by rw [Real.sq_sqrt hpos]
    rw [h_sqrt_pi_cube]
    rw [hg]
    dsimp
    rw [h_sq]
    dsimp [f', f]
    field_simp [hγ.ne']
  -- Apply the change-of-variables lemma
  calc
    (∫ t in Ioi (0 : ℝ), ((Real.sqrt (π / (γ + t ^ 2))) ^ 3) *
        Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * S))
      = (∫ t in Ioi (0 : ℝ), f' t * g (f t)) := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t using h_eq t
    _ = (∫ t in Ioi (0 : ℝ), f' t • g (f t)) := by
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with t; simp [smul_eq_mul]
    _ = (∫ u in f '' Ioi (0 : ℝ), g u) :=
      (integral_image_eq_integral_deriv_smul_of_monotoneOn
        measurableSet_Ioi h_deriv h_mono g).symm
    _ = (∫ u in Ioo (0 : ℝ) 1, g u) := by rw [h_image]
    _ = (∫ u in Ioc (0 : ℝ) 1, g u) := by rw [integral_Ioc_eq_integral_Ioo]
    _ = (∫ u in (0 : ℝ)..1, g u) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = ((Real.sqrt π) ^ 3 / γ) * (∫ u in (0 : ℝ)..1, Real.exp (-(γ * S) * u ^ 2)) := by
      rw [hg]
      simp [intervalIntegral.integral_const_mul]
    _ = ((Real.sqrt π) ^ 3 / γ) * boys0 (γ * S) := rfl

/-! ## 8. Core Coulomb identity -/

/-- The cubed `√(π/(γ+t²))` is integrable on `Ioi 0`: bounded on `Ioc 0 1` (continuous) and
dominated by `π^(3/2) · t^(-3)` on `Ioi 1`, both integrable. -/
private lemma integrableOn_sqrt_pi_div_pow3 (γ : ℝ) (hγ : 0 < γ) :
    IntegrableOn (fun t : ℝ => (Real.sqrt (π / (γ + t ^ 2))) ^ 3) (Ioi (0 : ℝ)) volume := by
  set g : ℝ → ℝ := fun t => (Real.sqrt (π / (γ + t ^ 2))) ^ 3
  have hg_cont : Continuous g := by
    refine (Real.continuous_sqrt.comp (continuous_const.div
      (continuous_const.add (continuous_id.pow 2)) ?_)).pow 3
    intro x
    have : 0 < γ + x ^ 2 := by nlinarith
    exact this.ne'
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from
    (Ioc_union_Ioi_eq_Ioi (le_of_lt (by norm_num : (0 : ℝ) < 1))).symm]
  refine IntegrableOn.union ?_ ?_
  · exact (hg_cont.continuousOn.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  · refine Integrable.mono' (g := fun t => π ^ ((3 : ℝ) / 2) * t ^ (-(3 : ℝ)))
      (Integrable.const_mul (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-(3 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 1)) _)
      hg_cont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with t (ht1 : (1 : ℝ) < t)
    have ht_pos : 0 < t := by linarith
    have h_t_sq : t ^ 2 ≤ γ + t ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h_le : (Real.sqrt (π / (γ + t ^ 2))) ^ 3 ≤ (Real.sqrt (π / t ^ 2)) ^ 3 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_left (by positivity) (by positivity) h_t_sq)) 3
    have h_sqrt_pi : (Real.sqrt π) ^ 3 = π ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) 3,
        ← Real.rpow_mul Real.pi_nonneg]
      norm_num
    have h_rhs : (Real.sqrt (π / t ^ 2)) ^ 3 = π ^ ((3 : ℝ) / 2) * t ^ (-(3 : ℝ)) := by
      rw [Real.sqrt_div Real.pi_nonneg, Real.sqrt_sq ht_pos.le, div_pow, h_sqrt_pi,
        show t ^ 3 = t ^ (3 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
        div_eq_mul_inv, ← Real.rpow_neg ht_pos.le]
    linarith

/-- For each `t`, the 3D Gaussian `exp(-γ|r|² - t²|r-A|²)` is integrable in `r`,
since it is dominated by the integrable `exp(-γ|r|²)`. -/
private lemma integrable_gaussian_combined (γ t : ℝ) (hγ : 0 < γ) (A : ℝ³) :
    Integrable (fun r : ℝ³ =>
      Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2)) volume := by
  have h_dom_int : Integrable (fun r : ℝ³ => Real.exp (-γ * ∑ i, (r i) ^ 2)) volume := by
    have h_eq : (fun r : ℝ³ => Real.exp (-γ * ∑ i, (r i) ^ 2)) =
                (fun r : ℝ³ => ∏ i, Real.exp (-γ * (r i) ^ 2)) := by
      funext r; rw [Finset.mul_sum, ← Real.exp_sum]
    rw [h_eq]
    exact MeasureTheory.Integrable.fintype_prod (μ := fun _ => volume)
      (fun _ => integrable_exp_neg_mul_sq hγ)
  refine h_dom_int.mono' (by fun_prop) ?_
  · refine Filter.Eventually.of_forall (fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have h_t2_nn : 0 ≤ t ^ 2 := sq_nonneg _
    have h_S_nn : 0 ≤ ∑ i : Fin 3, (r i - A i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have := mul_nonneg h_t2_nn h_S_nn
    linarith

/-- Integrability of `exp(-γ|r|² - t²|r-A|²)` on `ℝ³ × Ioi(0)` with respect to the product
Lebesgue measure. This justifies the Fubini swap in the nuclear-attraction identity.
The integrand is nonnegative, measurable, and its iterated integral (inner t, outer r)
equals the nuclear-attraction integral `∫ exp(-γ|r|²)/|r-A| dr`, which converges in ℝ³. -/
lemma integrable_prod_gaussian_coulomb (γ : ℝ) (hγ : 0 < γ) (A : ℝ³) :
    Integrable (Function.uncurry (fun (r : ℝ³) (t : ℝ) =>
      Real.exp (-γ * ∑ i, (r i) ^ 2) *
      ((Ioi (0 : ℝ)).indicator (fun t' : ℝ => Real.exp (-(∑ i, (r i - A i) ^ 2) * t' ^ 2)) t)))
      (volume.prod volume) := by
  set f : ℝ³ × ℝ → ℝ := fun p =>
      Real.exp (-γ * ∑ i, (p.1 i) ^ 2) *
      ((Ioi (0 : ℝ)).indicator
        (fun t' : ℝ => Real.exp (-(∑ i, (p.1 i - A i) ^ 2) * t' ^ 2)) p.2)
    with hfdef
  change Integrable f (volume.prod volume)
  -- Rewrite `f` as a single indicator of a jointly continuous Gaussian.
  have hf_eq : f = ({p : ℝ³ × ℝ | p.2 ∈ Ioi (0 : ℝ)}).indicator
      (fun p => Real.exp (-γ * ∑ i, (p.1 i) ^ 2) *
                Real.exp (-(∑ i, (p.1 i - A i) ^ 2) * p.2 ^ 2)) := by
    funext p
    simp only [hfdef, Set.indicator_apply, mem_setOf_eq, mem_Ioi]
    split_ifs <;> simp
  have hf_meas : Measurable f := by
    rw [hf_eq]
    refine Measurable.indicator ?_ (measurable_snd measurableSet_Ioi)
    fun_prop
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    change 0 ≤ Real.exp _ * _
    refine mul_nonneg (Real.exp_nonneg _) ?_
    by_cases ht : p.2 ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht]; exact Real.exp_nonneg _
    · rw [Set.indicator_of_notMem ht]
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf_nonneg)]
  have h_aemeas : AEMeasurable (fun p => ENNReal.ofReal (f p)) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.measurable.comp hf_meas).aemeasurable
  -- Tonelli (outer t, inner r), then bound the inner Gaussian integral via Lemma 5.
  rw [lintegral_prod_symm _ h_aemeas]
  have h_inner_le : ∀ t : ℝ, ∫⁻ r, ENNReal.ofReal (f (r, t)) ∂volume ≤
      (Ioi (0 : ℝ)).indicator
        (fun t : ℝ => ENNReal.ofReal ((Real.sqrt (π / (γ + t ^ 2))) ^ 3)) t := by
    intro t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · have h_inner_eq : ∀ r : ℝ³, f (r, t) =
          Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2) := by
        intro r
        change Real.exp _ * _ = _
        rw [Set.indicator_of_mem ht, ← Real.exp_add]
        congr 1; ring
      have hcongr : (fun r => ENNReal.ofReal (f (r, t))) =
          (fun r => ENNReal.ofReal
            (Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2))) := by
        funext r; rw [h_inner_eq]
      rw [hcongr,
        ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussian_combined γ t hγ A)
          (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)),
        integral_exp_combined_3d γ t hγ A, Set.indicator_of_mem ht]
      refine ENNReal.ofReal_le_ofReal ?_
      have h_pow_nn : 0 ≤ (Real.sqrt (π / (γ + t ^ 2))) ^ 3 := by positivity
      have h_exp_le_one :
          Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * ∑ i : Fin 3, (A i) ^ 2) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have h_pos : 0 < γ + t ^ 2 := by nlinarith
        have h_S_nn : 0 ≤ ∑ i : Fin 3, (A i) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have h_factor_nn : 0 ≤ γ * t ^ 2 := by positivity
        have h_inside : 0 ≤ γ * t ^ 2 / (γ + t ^ 2) := div_nonneg h_factor_nn h_pos.le
        have h_neg : -(γ * t ^ 2) / (γ + t ^ 2) ≤ 0 := by rw [neg_div]; linarith
        exact mul_nonpos_of_nonpos_of_nonneg h_neg h_S_nn
      have hmul := mul_le_mul_of_nonneg_left h_exp_le_one h_pow_nn
      linarith
    · have h_zero : ∀ r, f (r, t) = 0 := by
        intro r; change Real.exp _ * _ = _
        rw [Set.indicator_of_notMem ht, mul_zero]
      simp only [h_zero, ENNReal.ofReal_zero, lintegral_zero]
      rw [Set.indicator_of_notMem ht]
  calc ∫⁻ t, ∫⁻ r, ENNReal.ofReal (f (r, t)) ∂volume ∂volume
      ≤ ∫⁻ t, (Ioi (0 : ℝ)).indicator
          (fun t : ℝ => ENNReal.ofReal ((Real.sqrt (π / (γ + t ^ 2))) ^ 3)) t ∂volume :=
        lintegral_mono h_inner_le
    _ = ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal ((Real.sqrt (π / (γ + t ^ 2))) ^ 3) ∂volume :=
        lintegral_indicator measurableSet_Ioi _
    _ < ⊤ := IntegrableOn.setLIntegral_lt_top (integrableOn_sqrt_pi_div_pow3 γ hγ)

/-- Core Coulomb–Gaussian identity: for `0 < γ`,
  `∫ exp(-γ‖r‖²) · (1/‖r-A‖) dr = (2π/γ) · boys0(γ · ‖A‖²)`.

This is the building block of both the nuclear-attraction and electron-repulsion integrals: the
Coulomb kernel is replaced by its AE Gaussian form, the integrals are swapped (Fubini, justified
by `integrable_prod_gaussian_coulomb`), the inner 3D Gaussian is evaluated
(`integral_exp_combined_3d`), and the remaining 1D integral is reduced to `boys0` by the change
of variables of section 7. -/
lemma integral_exp_neg_mul_sq_coulomb (γ : ℝ) (hγ : 0 < γ) (A : ℝ³) :
    (∫ r : ℝ³, Real.exp (-γ * ∑ i, (r i) ^ 2) * coulomb r A) = (2 * π / γ) * boys0 (γ * ∑ i, (A i) ^ 2) := by
  set S := ∑ i : Fin 3, (A i) ^ 2 with hS
  -- Step 1: Replace coulomb by its AE integral representation (Lemma 6)
  have h_coulomb_ae := coulomb_eq_integral_ae A
  have h_int_ae : (fun r => Real.exp (-γ * ∑ i, (r i) ^ 2) * coulomb r A) =ᵐ[volume]
      fun r => (2 / Real.sqrt π) * (Real.exp (-γ * ∑ i, (r i) ^ 2) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-(∑ i, (r i - A i) ^ 2) * t ^ 2))) := by
    filter_upwards [h_coulomb_ae] with r hr
    rw [hr]; ring
  rw [integral_congr_ae h_int_ae, integral_const_mul]
  -- Step 2: Swap the r and t integrals via Fubini
  have h_int := integrable_prod_gaussian_coulomb γ hγ A
  have h_swap : (∫ r : ℝ³, Real.exp (-γ * ∑ i, (r i) ^ 2) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-(∑ i, (r i - A i) ^ 2) * t ^ 2))) =
      (∫ t in Ioi (0 : ℝ), (∫ r : ℝ³,
        Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2))) := by
    set f := fun (r : ℝ³) => Real.exp (-γ * ∑ i, (r i) ^ 2) with hf
    set g := fun (r : ℝ³) (t : ℝ) => Real.exp (-(∑ i, (r i - A i) ^ 2) * t ^ 2) with hg
    calc
      (∫ r : ℝ³, f r * (∫ t in Ioi (0 : ℝ), g r t))
        = (∫ r : ℝ³, (∫ t : ℝ, f r *
            ((Ioi (0 : ℝ)).indicator (g r) t))) := by
          refine integral_congr_ae ?_
          filter_upwards with r
          rw [(integral_indicator measurableSet_Ioi (μ := volume) (f := g r)).symm, integral_const_mul]
      _ = (∫ t : ℝ, (∫ r : ℝ³, f r *
            ((Ioi (0 : ℝ)).indicator (g r) t))) :=
        integral_integral_swap h_int
      _ = (∫ t : ℝ, ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) *
            (∫ r : ℝ³, f r * g r t)) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          have h_ind_mul (r : ℝ³) : ((Ioi (0 : ℝ)).indicator (g r) t) =
              ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) * g r t := by
            by_cases ht : t ∈ Ioi (0 : ℝ)
            · simp [Set.indicator, ht]
            · simp [Set.indicator, ht]
          calc
            (∫ r : ℝ³, f r * ((Ioi (0 : ℝ)).indicator (g r) t))
                = (∫ r : ℝ³, f r * (((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) * g r t)) := by
              refine integral_congr_ae ?_
              filter_upwards with r
              rw [h_ind_mul r]
            _ = (∫ r : ℝ³, ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) * (f r * g r t)) := by
              refine integral_congr_ae ?_
              filter_upwards with r; ring
            _ = ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) *
                (∫ r : ℝ³, f r * g r t) := by
              rw [integral_const_mul]
      _ = (∫ t : ℝ, ((Ioi (0 : ℝ)).indicator (fun t' => (∫ r : ℝ³, f r * g r t'))) t) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simp [Set.indicator, Set.mem_Ioi]
      _ = (∫ t in Ioi (0 : ℝ), (∫ r : ℝ³, f r * g r t)) :=
        integral_indicator measurableSet_Ioi
      _ = (∫ t in Ioi (0 : ℝ), (∫ r : ℝ³,
            Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2))) := by
          refine setIntegral_congr_ae measurableSet_Ioi ?_
          filter_upwards with t ht
          refine integral_congr_ae ?_
          filter_upwards with r
          dsimp [f, g]
          rw [← Real.exp_add]
          ring_nf
  rw [h_swap]
  -- Step 3: Apply the 3D Gaussian integral formula (Lemma 5)
  have h_inner (t : ℝ) : (∫ r : ℝ³,
      Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2)) =
      ((Real.sqrt (π / (γ + t ^ 2))) ^ 3) *
        Real.exp (-(γ * t ^ 2) / (γ + t ^ 2) * S) := by
    rw [integral_exp_combined_3d γ t hγ A, hS]
  simp_rw [h_inner]
  -- Step 4: Change of variables in the remaining 1D integral
  rw [integral_Ioi_gaussian_sqrt_to_boys0 γ S hγ]
  -- Step 5: Simplify the constant factor
  calc
    (2 / Real.sqrt π) * (((Real.sqrt π) ^ 3 / γ) * boys0 (γ * S))
        = ((2 / Real.sqrt π) * ((Real.sqrt π) ^ 3 / γ)) * boys0 (γ * S) := by ring
    _ = (2 * π / γ) * boys0 (γ * S) := by
      have h_sqrt_sq : (Real.sqrt π) ^ 2 = π := Real.sq_sqrt (by positivity : 0 ≤ π)
      field_simp
      ring_nf
      rw [h_sqrt_sq]
      ring
    _ = (2 * π / γ) * boys0 (γ * ∑ i : Fin 3, (A i) ^ 2) := by rw [hS]

/-! ## 9. Nuclear attraction integral -/

/-- Closed form of the s-type nuclear-attraction integral. For `0 < α`, `0 < β`,
  `⟨φ_α^{R₁} | 1/‖r-C‖ | φ_β^{R₂}⟩ = (2π/(α+β)) · K · boys0((α+β) · ‖P - C‖²)`,
where `P = (αR₁+βR₂)/(α+β)` is the Gaussian product center and
`K = exp(-αβ/(α+β) · ‖R₁-R₂‖²)` is the product-theorem prefactor. The Gaussian product theorem
collapses the two-center bra-ket to a single Gaussian at `P` against the nucleus at `C`, after
which `integral_exp_neg_mul_sq_coulomb` applies. -/
theorem nuclearAttraction_primitiveGTO_s
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (R₁ R₂ C : ℝ³) :
    nuclearAttraction C (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) =
      (2 * π / (α + β)) *
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        boys0 ((α + β) * ∑ i : Fin 3, ((α * R₁ i + β * R₂ i) / (α + β) - C i) ^ 2) := by
  set γ := α + β with hγ
  have hγpos : 0 < γ := by linarith
  set K := Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) with hK
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / γ with hP
  have h_prod (r : ℝ³) : primitiveGTO_s α R₁ r * primitiveGTO_s β R₂ r = K * Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    dsimp [K, P, γ]
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have hsq : ∀ x a b : ℝ, -α * (x - a) ^ 2 + -β * (x - b) ^ 2 =
        -(α * β) / (α + β) * (a - b) ^ 2 + -(α + β) * (x - (α * a + β * b) / (α + β)) ^ 2 := by
      intro x a b; field_simp [show α + β ≠ 0 from by linarith]; ring
    calc
      -α * ∑ i : Fin 3, (r i - R₁ i) ^ 2 + -β * ∑ i : Fin 3, (r i - R₂ i) ^ 2
          = ∑ i : Fin 3, (-α * (r i - R₁ i) ^ 2 + -β * (r i - R₂ i) ^ 2) := by
            simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α * β) / (α + β) * (R₁ i - R₂ i) ^ 2 + -(α + β) * (r i - P i) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            dsimp [P]; rw [hsq (r i) (R₁ i) (R₂ i)]
      _ = (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) + (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  unfold nuclearAttraction
  calc
    (∫ r : ℝ³, primitiveGTO_s α R₁ r * coulomb r C * primitiveGTO_s β R₂ r)
        = (∫ r : ℝ³, (primitiveGTO_s α R₁ r * primitiveGTO_s β R₂ r) * coulomb r C) := by
          refine integral_congr_ae ?_; filter_upwards with r; ring
    _ = (∫ r : ℝ³, K * (Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) * coulomb r C)) := by
      refine integral_congr_ae ?_
      filter_upwards with r; rw [h_prod r]; ring
    _ = K * (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) * coulomb r C) := by
      rw [integral_const_mul]
    _ = K * (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) * coulomb r (C - P)) := by
      have h_coulomb_sub : ∀ r, coulomb (r - P) (C - P) = coulomb r C := by
        intro r
        calc
          coulomb (r - P) (C - P) = 1 / Real.sqrt (∑ i, ((r - P) i - (C - P) i) ^ 2) := rfl
          _ = 1 / Real.sqrt (∑ i, (r i - C i) ^ 2) := by
            congr 1
            simp [Pi.sub_apply]
          _ = coulomb r C := rfl
      have h_int_eq : (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) * coulomb r C) =
          (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) * coulomb r (C - P)) := by
        have h_trans := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
          (fun r : ℝ³ => Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) * coulomb r (C - P)) P
        calc
          (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) * coulomb r C) =
              (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i - P i) ^ 2) * coulomb (r - P) (C - P)) := by
            refine integral_congr_ae ?_
            filter_upwards with r; rw [h_coulomb_sub r]
          _ = (∫ r : ℝ³, Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) * coulomb r (C - P)) := by
            simpa [Pi.sub_apply] using h_trans
      rw [h_int_eq]
    _ = K * ((2 * π / γ) * boys0 (γ * ∑ i : Fin 3, ((C - P) i) ^ 2)) := by
      rw [integral_exp_neg_mul_sq_coulomb γ hγpos (C - P)]
    _ = (2 * π / (α + β)) * Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        boys0 ((α + β) * ∑ i : Fin 3, ((α * R₁ i + β * R₂ i) / (α + β) - C i) ^ 2) := by
      dsimp [K, P, γ]
      have h_sum_eq : (∑ i : Fin 3, ((C - fun i => (α * R₁ i + β * R₂ i) / (α + β)) i) ^ 2) =
          (∑ i : Fin 3, ((α * R₁ i + β * R₂ i) / (α + β) - C i) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [Pi.sub_apply]; ring
      calc
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
            ((2 * π / (α + β)) * boys0 ((α + β) * ∑ i : Fin 3, ((C - fun i => (α * R₁ i + β * R₂ i) / (α + β)) i) ^ 2))
            = (2 * π / (α + β)) * Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
              boys0 ((α + β) * ∑ i : Fin 3, ((C - fun i => (α * R₁ i + β * R₂ i) / (α + β)) i) ^ 2) := by ring
        _ = (2 * π / (α + β)) * Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
              boys0 ((α + β) * ∑ i : Fin 3, ((α * R₁ i + β * R₂ i) / (α + β) - C i) ^ 2) := by rw [h_sum_eq]

/-! ## 10. Change of variables for the ERI identity -/

/-- Variant of `hasDerivAt_u_div_sqrt_add_sq` with a weighted quadratic `q + p·x²`
(`q > 0`, `p ≥ 0`): `d/dx[x/√(q+p·x²)] = q/(q+p·x²)^(3/2)`. -/
private lemma hasDerivAt_u_div_sqrt_add_p_sq (q p u : ℝ) (hq : 0 < q) (hp : 0 ≤ p) :
    HasDerivAt (fun x : ℝ => x / Real.sqrt (q + p * x ^ 2))
      (q / (q + p * u ^ 2) ^ (3/2 : ℝ)) u := by
  have h_add_pos : 0 < q + p * u ^ 2 := by nlinarith
  have h_sqrt_ne : Real.sqrt (q + p * u ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h_add_pos).ne'
  have h_ne : q + p * u ^ 2 ≠ 0 := h_add_pos.ne'
  have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    simpa [sq, two_mul] using (hasDerivAt_id u).mul (hasDerivAt_id u)
  have h_pu2 : HasDerivAt (fun x : ℝ => p * x ^ 2) (p * (2 * u)) u := h_sq.const_mul p
  have h_add_deriv : HasDerivAt (fun x : ℝ => q + p * x ^ 2) (p * (2 * u)) u := h_pu2.const_add q
  have h_denom_deriv : HasDerivAt (fun x : ℝ => Real.sqrt (q + p * x ^ 2))
      (p * u / Real.sqrt (q + p * u ^ 2)) u := by
    have h_sqrt_deriv : HasDerivAt Real.sqrt ((2 * Real.sqrt (q + p * u ^ 2))⁻¹) (q + p * u ^ 2) := by
      simpa [one_div] using hasDerivAt_sqrt (by nlinarith : q + p * u ^ 2 ≠ 0)
    have h_comp := HasDerivAt.comp u h_sqrt_deriv h_add_deriv
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_comp
  have h_div := HasDerivAt.div (hasDerivAt_id u) h_denom_deriv h_sqrt_ne
  refine h_div.congr_deriv ?_
  have h_sq_sqrt : Real.sqrt (q + p * u ^ 2) ^ 2 = q + p * u ^ 2 := Real.sq_sqrt (by nlinarith)
  have h_pow_eq : (q + p * u ^ 2) ^ (3/2 : ℝ) = Real.sqrt (q + p * u ^ 2) ^ 3 := by
    calc (q + p * u ^ 2) ^ (3/2 : ℝ)
        = (q + p * u ^ 2) ^ ((1/2 : ℝ) * (3 : ℝ)) := by norm_num
      _ = ((q + p * u ^ 2) ^ (1/2 : ℝ)) ^ (3 : ℝ) := by
        rw [rpow_mul (by nlinarith : 0 ≤ q + p * u ^ 2) (1/2 : ℝ) (3 : ℝ)]
      _ = (Real.sqrt (q + p * u ^ 2)) ^ (3 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (Real.sqrt (q + p * u ^ 2)) ^ 3 := by norm_num
  simp only [Function.id_def]
  rw [h_pow_eq]
  field_simp [h_sqrt_ne, h_ne]
  rw [h_sq_sqrt]
  ring

/-- Change of variables `v = u·√((p+q)/(q+p·u²))` on `[0,1]`, used by the ERI identity
`integral_double_exp_coulomb`. Maps `[0,1]` onto `[0,1]` with `φ 0 = 0`, `φ 1 = 1`;
the Jacobian `φ'` cancels the prefactor exactly. -/
private lemma integral_Icc_gaussian_to_boys0 (p q S : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ u in (0:ℝ)..1, ((Real.sqrt (π / (q + p * u ^ 2))) ^ 3) *
      Real.exp (-(p * q * u ^ 2) / (q + p * u ^ 2) * S)) =
    ((Real.sqrt π) ^ 3 / (q * Real.sqrt (p + q))) * boys0 (p * q / (p + q) * S) := by
  set φ : ℝ → ℝ := fun u => Real.sqrt (p + q) * (u / Real.sqrt (q + p * u ^ 2)) with hφ
  set φ' : ℝ → ℝ := fun u => Real.sqrt (p + q) * q / (Real.sqrt (q + p * u ^ 2)) ^ 3 with hφ'
  set ρ : ℝ := p * q / (p + q) with hρ
  set C : ℝ := (Real.sqrt π) ^ 3 / (q * Real.sqrt (p + q)) with hC
  set g : ℝ → ℝ := fun v => C * Real.exp (-(ρ * S) * v ^ 2) with hg
  have hpq_pos : 0 < p + q := by linarith
  have h_pow3 (u : ℝ) : (q + p * u ^ 2) ^ (3/2 : ℝ) = (Real.sqrt (q + p * u ^ 2)) ^ 3 := by
    have hpos : 0 ≤ q + p * u ^ 2 := by nlinarith
    calc (q + p * u ^ 2) ^ (3/2 : ℝ)
        = (q + p * u ^ 2) ^ ((1/2 : ℝ) * (3 : ℝ)) := by norm_num
      _ = ((q + p * u ^ 2) ^ (1/2 : ℝ)) ^ (3 : ℝ) := by
        rw [rpow_mul hpos (1/2 : ℝ) (3 : ℝ)]
      _ = (Real.sqrt (q + p * u ^ 2)) ^ (3 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (Real.sqrt (q + p * u ^ 2)) ^ 3 := by norm_num
  have hφ_deriv (u : ℝ) : HasDerivAt φ (φ' u) u := by
    dsimp [φ]
    have hu := hasDerivAt_u_div_sqrt_add_p_sq q p u hq hp.le
    convert HasDerivAt.const_mul (Real.sqrt (p + q)) hu using 1
    dsimp [φ']; rw [h_pow3 u]; ring
  have hφ'_cont : ContinuousOn φ' (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    dsimp [φ']
    have h_denom : ContinuousOn (fun u : ℝ => (Real.sqrt (q + p * u ^ 2)) ^ 3) (Icc 0 1) := by fun_prop
    have h_pos : ∀ u ∈ Icc (0:ℝ) 1, (Real.sqrt (q + p * u ^ 2)) ^ 3 ≠ 0 := by
      intro u _; positivity
    exact ContinuousOn.div continuousOn_const h_denom h_pos
  have hφ_0 : φ 0 = 0 := by dsimp [φ]; ring
  have hφ_1 : φ 1 = 1 := by
    dsimp [φ]
    have h1 : q + p * 1 ^ 2 = p + q := by rw [pow_two]; ring
    rw [h1]; field_simp [(Real.sqrt_pos.mpr hpq_pos).ne']
  have hg_cont : Continuous g := by dsimp [g]; fun_prop
  have h_eq (u : ℝ) :
      ((Real.sqrt (π / (q + p * u ^ 2))) ^ 3) *
        Real.exp (-(p * q * u ^ 2) / (q + p * u ^ 2) * S) =
      g (φ u) * φ' u := by
    have hpos : 0 ≤ q + p * u ^ 2 := by nlinarith
    have h_φ_sq : (φ u) ^ 2 = (p + q) * u ^ 2 / (q + p * u ^ 2) := by
      dsimp [φ]
      have h1 : (Real.sqrt (p + q)) ^ 2 = p + q := Real.sq_sqrt (by linarith)
      have h2 : (Real.sqrt (q + p * u ^ 2)) ^ 2 = q + p * u ^ 2 := Real.sq_sqrt hpos
      rw [show (Real.sqrt (p + q) * (u / Real.sqrt (q + p * u ^ 2))) ^ 2 =
          (Real.sqrt (p + q)) ^ 2 * (u / Real.sqrt (q + p * u ^ 2)) ^ 2 from by ring,
        h1,
        show (u / Real.sqrt (q + p * u ^ 2)) ^ 2 = u ^ 2 / (Real.sqrt (q + p * u ^ 2)) ^ 2
          from by ring,
        h2]
      field_simp
    have h_sqrt_pi_cube : (Real.sqrt (π / (q + p * u ^ 2))) ^ 3 =
        ((Real.sqrt π) ^ 3) / ((Real.sqrt (q + p * u ^ 2)) ^ 3) := by
      rw [Real.sqrt_div (by positivity : 0 ≤ π) _]; ring
    have h_exp : -(p * q * u ^ 2) / (q + p * u ^ 2) * S = -(ρ * S) * (φ u) ^ 2 := by
      rw [hρ, h_φ_sq]; field_simp
    rw [h_sqrt_pi_cube, h_exp, hg, hC, hρ, hφ, hφ']
    field_simp
  calc (∫ u in (0:ℝ)..1, ((Real.sqrt (π / (q + p * u ^ 2))) ^ 3) *
      Real.exp (-(p * q * u ^ 2) / (q + p * u ^ 2) * S))
      = (∫ u in (0:ℝ)..1, g (φ u) * φ' u) := by
        exact intervalIntegral.integral_congr (fun u _ => h_eq u)
    _ = (∫ u in φ 0..φ 1, g u) := by
      exact intervalIntegral.integral_comp_mul_deriv
        (fun u _ => hφ_deriv u) hφ'_cont hg_cont
    _ = (∫ u in (0:ℝ)..1, g u) := by rw [hφ_0, hφ_1]
    _ = C * (∫ u in (0:ℝ)..1, Real.exp (-(ρ * S) * u ^ 2)) := by
      rw [hg, intervalIntegral.integral_const_mul]
    _ = C * boys0 (ρ * S) := rfl
    _ = ((Real.sqrt π) ^ 3 / (q * Real.sqrt (p + q))) * boys0 (p * q / (p + q) * S) := by
      rw [hC, hρ]

/-- Variant of `integral_exp_combined_3d` taking the second Gaussian's coefficient `c`
directly (with `0 ≤ c`) instead of `t ^ 2`, avoiding `√` plumbing. -/
private lemma integral_exp_combined_3d_nonneg (γ c : ℝ) (hγ : 0 < γ) (hc : 0 ≤ c) (A : ℝ³) :
    (∫ r : ℝ³, Real.exp (-γ * ∑ i, (r i) ^ 2 - c * ∑ i, (r i - A i) ^ 2)) =
    (Real.sqrt (π / (γ + c))) ^ 3 *
      Real.exp (-(γ * c) / (γ + c) * ∑ i : Fin 3, (A i) ^ 2) := by
  set t := Real.sqrt c with ht
  have htc : t ^ 2 = c := by rw [ht, Real.sq_sqrt hc]
  have h_eq : (fun r : ℝ³ => Real.exp (-γ * ∑ i, (r i) ^ 2 - c * ∑ i, (r i - A i) ^ 2)) =
              (fun r : ℝ³ => Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2)) := by
    funext r; rw [htc]
  rw [h_eq, integral_exp_combined_3d γ t hγ A, htc]

/-! ## 11. Electron repulsion integral -/

/-- Closed form of the s-type two-electron repulsion integral (ERI). For positive exponents,
  `(φ₁ φ₂ | φ₃ φ₄) = (2 π^(5/2)) / (p · q · √(p+q)) · K₁ · K₂ · boys0(pq/(p+q) · ‖P-Q‖²)`,
where `p = α₁+α₂`, `q = α₃+α₄` are the pair exponents, `P = (α₁R₁+α₂R₂)/p`,
`Q = (α₃R₃+α₄R₄)/q` the pair product centers, and `K₁`, `K₂` the product-theorem prefactors.
The inner `r₂` integral is a nuclear-attraction-type integral yielding `boys0(q·‖r₁-Q‖²)`; the
outer `r₁` integral is then a second Coulomb–Gaussian identity (via the change of variables of
section 10) yielding `boys0(pq/(p+q)·‖P-Q‖²)`. -/
theorem electronRepulsion_primitiveGTO_s
    (α₁ α₂ α₃ α₄ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα₃ : 0 < α₃) (hα₄ : 0 < α₄)
    (R₁ R₂ R₃ R₄ : ℝ³) :
    electronRepulsion (primitiveGTO_s α₁ R₁) (primitiveGTO_s α₂ R₂)
        (primitiveGTO_s α₃ R₃) (primitiveGTO_s α₄ R₄) =
      (2 * π ^ (5/2 : ℝ)) /
        ((α₁ + α₂) * (α₃ + α₄) * Real.sqrt ((α₁ + α₂) + (α₃ + α₄))) *
        Real.exp (-(α₁ * α₂) / (α₁ + α₂) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        Real.exp (-(α₃ * α₄) / (α₃ + α₄) * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) *
        boys0 ((α₁ + α₂) * (α₃ + α₄) / ((α₁ + α₂) + (α₃ + α₄)) *
          ∑ i : Fin 3, (((α₁ * R₁ i + α₂ * R₂ i) / (α₁ + α₂)) -
            ((α₃ * R₃ i + α₄ * R₄ i) / (α₃ + α₄))) ^ 2) := by
  -- Abbreviations
  set p : ℝ := α₁ + α₂ with hp
  set q : ℝ := α₃ + α₄ with hq
  have hp_pos : 0 < p := by dsimp [p]; linarith
  have hq_pos : 0 < q := by dsimp [q]; linarith
  have hpq_pos : 0 < p + q := by linarith
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_ne : q ≠ 0 := hq_pos.ne'
  set P : ℝ³ := fun i => (α₁ * R₁ i + α₂ * R₂ i) / p with hP
  set Q : ℝ³ := fun i => (α₃ * R₃ i + α₄ * R₄ i) / q with hQ
  set K₁ : ℝ := Real.exp (-(α₁ * α₂) / p * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) with hK1
  set K₂ : ℝ := Real.exp (-(α₃ * α₄) / q * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) with hK2
  -- Step 1: combine the two products of s-type GTOs (mirror nuclearAttraction `h_prod`).
  have hsq12 : ∀ x a b : ℝ, -α₁ * (x - a) ^ 2 + -α₂ * (x - b) ^ 2 =
      -(α₁ * α₂) / (α₁ + α₂) * (a - b) ^ 2 + -(α₁ + α₂) * (x - (α₁ * a + α₂ * b) / (α₁ + α₂)) ^ 2 := by
    intro x a b; field_simp [hp_ne]; ring
  have hsq34 : ∀ x a b : ℝ, -α₃ * (x - a) ^ 2 + -α₄ * (x - b) ^ 2 =
      -(α₃ * α₄) / (α₃ + α₄) * (a - b) ^ 2 + -(α₃ + α₄) * (x - (α₃ * a + α₄ * b) / (α₃ + α₄)) ^ 2 := by
    intro x a b; field_simp [hq_ne]; ring
  have h_prod12 (r : ℝ³) :
      primitiveGTO_s α₁ R₁ r * primitiveGTO_s α₂ R₂ r =
        K₁ * Real.exp (-p * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    dsimp [K₁, P, p]
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one,
      one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      -α₁ * ∑ i : Fin 3, (r i - R₁ i) ^ 2 + -α₂ * ∑ i : Fin 3, (r i - R₂ i) ^ 2
          = ∑ i : Fin 3, (-α₁ * (r i - R₁ i) ^ 2 + -α₂ * (r i - R₂ i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3,
            (-(α₁ * α₂) / (α₁ + α₂) * (R₁ i - R₂ i) ^ 2 +
              -(α₁ + α₂) * (r i - P i) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_); dsimp [P]; rw [hsq12 (r i) (R₁ i) (R₂ i)]
      _ = (-(α₁ * α₂) / (α₁ + α₂) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) +
            (-(α₁ + α₂) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  have h_prod34 (r : ℝ³) :
      primitiveGTO_s α₃ R₃ r * primitiveGTO_s α₄ R₄ r =
        K₂ * Real.exp (-q * ∑ i : Fin 3, (r i - Q i) ^ 2) := by
    dsimp [K₂, Q, q]
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one,
      one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      -α₃ * ∑ i : Fin 3, (r i - R₃ i) ^ 2 + -α₄ * ∑ i : Fin 3, (r i - R₄ i) ^ 2
          = ∑ i : Fin 3, (-α₃ * (r i - R₃ i) ^ 2 + -α₄ * (r i - R₄ i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3,
            (-(α₃ * α₄) / (α₃ + α₄) * (R₃ i - R₄ i) ^ 2 +
              -(α₃ + α₄) * (r i - Q i) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_); dsimp [Q]; rw [hsq34 (r i) (R₃ i) (R₄ i)]
      _ = (-(α₃ * α₄) / (α₃ + α₄) * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) +
            (-(α₃ + α₄) * ∑ i : Fin 3, (r i - Q i) ^ 2) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  -- Coulomb symmetry: coulomb x y = coulomb y x.
  have h_coulomb_sym (x y : ℝ³) : coulomb x y = coulomb y x := by
    show 1 / Real.sqrt (∑ i, (x i - y i) ^ 2) = 1 / Real.sqrt (∑ i, (y i - x i) ^ 2)
    refine congr_arg (fun t => 1 / Real.sqrt t) ?_
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- Coulomb translation invariance: coulomb (x - a) (y - a) = coulomb x y.
  have h_coulomb_trans (a x y : ℝ³) : coulomb (x - a) (y - a) = coulomb x y := by
    show 1 / Real.sqrt (∑ i, ((x - a) i - (y - a) i) ^ 2) = 1 / Real.sqrt (∑ i, (x i - y i) ^ 2)
    refine congr_arg (fun t => 1 / Real.sqrt t) ?_
    refine Finset.sum_congr rfl (fun i _ => ?_); simp [Pi.sub_apply]
  -- Step 2: compute the inner r₂ integral, pointwise in r₁.
  have h_inner_r2 (r₁ : ℝ³) :
      (∫ r₂ : ℝ³, coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) =
        K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)) := by
    have h_reassoc :
        (fun r₂ : ℝ³ => coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) =
          (fun r₂ : ℝ³ => K₂ * (coulomb r₁ r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2))) := by
      funext r₂
      calc coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂
          = coulomb r₁ r₂ * (primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) := by ring
        _ = K₂ * (coulomb r₁ r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) := by
          rw [h_prod34 r₂]; ring
    rw [h_reassoc, integral_const_mul]
    have h_coul_trans_shift : ∀ r₂, coulomb r₁ r₂ = coulomb (r₁ - Q) (r₂ - Q) :=
      fun r₂ => (h_coulomb_trans Q r₁ r₂).symm
    have h_inner :
        (∫ r₂ : ℝ³, coulomb r₁ r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) =
          (2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) := by
      -- Translate coulomb r₁ r₂ to coulomb (r₁-Q)(r₂-Q), shift r₂ by Q.
      have h_step1 : (∫ r₂ : ℝ³, coulomb r₁ r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) =
          (∫ r₂ : ℝ³, coulomb (r₁ - Q) (r₂ - Q) * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) := by
        refine integral_congr_ae ?_; filter_upwards with r₂; rw [h_coul_trans_shift r₂]
      rw [h_step1]
      -- Shift the integration variable r₂ by Q via integral_sub_right_eq_self.
      have h_trans : (∫ r₂ : ℝ³, coulomb (r₁ - Q) (r₂ - Q) * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) =
          (∫ r₂ : ℝ³, coulomb (r₁ - Q) r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i) ^ 2)) := by
        have h_eq := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
          (fun r : ℝ³ => coulomb (r₁ - Q) r * Real.exp (-q * ∑ i : Fin 3, (r i) ^ 2)) Q
        rw [← h_eq]
        refine integral_congr_ae ?_
        filter_upwards with r₂
        simp only [Pi.sub_apply]
      rw [h_trans]
      -- Swap coulomb args (symmetry) and apply the Coulomb-Gaussian lemma.
      rw [show (∫ r₂ : ℝ³, coulomb (r₁ - Q) r₂ * Real.exp (-q * ∑ i : Fin 3, (r₂ i) ^ 2)) =
            (∫ r₂ : ℝ³, Real.exp (-q * ∑ i : Fin 3, (r₂ i) ^ 2) * coulomb r₂ (r₁ - Q)) by
        refine integral_congr_ae ?_; filter_upwards with r₂
        rw [h_coulomb_sym (r₁ - Q) r₂]; ring]
      rw [integral_exp_neg_mul_sq_coulomb q hq_pos (r₁ - Q)]
      simp only [Pi.sub_apply]
    rw [h_inner]
  -- Step 3: rewrite the outer r₁ integral using h_inner_r2, pull out constants.
  unfold electronRepulsion
  have h_reassoc_outer :
      (fun r₁ : ℝ³ => ∫ r₂ : ℝ³,
        primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ * coulomb r₁ r₂ *
          primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) =
      (fun r₁ : ℝ³ => primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
        (∫ r₂ : ℝ³, coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂)) := by
    funext r₁
    rw [show (∫ r₂ : ℝ³,
          primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ * coulomb r₁ r₂ *
            primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) =
        (∫ r₂ : ℝ³, (primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁) *
          (coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂)) by
      refine integral_congr_ae ?_; filter_upwards with r₂; ring,
      integral_const_mul]
  rw [h_reassoc_outer]
  rw [show (∫ r₁ : ℝ³, primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
        (∫ r₂ : ℝ³, coulomb r₁ r₂ * primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂)) =
      (∫ r₁ : ℝ³, primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
        (K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) by
    refine integral_congr_ae ?_; filter_upwards with r₁; rw [h_inner_r2 r₁]]
  rw [show (∫ r₁ : ℝ³, primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
        (K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) =
      (∫ r₁ : ℝ³, (K₁ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) *
        (K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) by
    refine integral_congr_ae ?_; filter_upwards with r₁; rw [h_prod12 r₁]]
  -- Pull K₁ * K₂ * (2π/q) out of the integral.
  rw [show (∫ r₁ : ℝ³, (K₁ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) *
        (K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) =
      K₁ * (K₂ * ((2 * π / q) *
        (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) by
    rw [show (∫ r₁ : ℝ³, (K₁ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) *
          (K₂ * ((2 * π / q) * boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)))) =
        (∫ r₁ : ℝ³, K₁ * (K₂ * ((2 * π / q) *
          (Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
            boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))))) by
        refine integral_congr_ae ?_; filter_upwards with r₁; ring,
      integral_const_mul, integral_const_mul, integral_const_mul]]
  -- Step 4: Fubini swap ℝ³ × [0,1]. Expand boys0 as an interval integral and swap.
  have h_SPQ : ∑ i : Fin 3, ((P - Q) i) ^ 2 = ∑ i : Fin 3, ((Q - P) i) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_); simp [Pi.sub_apply]; ring
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h_swap :
      (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
        boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)) =
      (∫ u in (0:ℝ)..1, (∫ r₁ : ℝ³,
        Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 -
          (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) := by
    -- boys0 t = ∫ u in 0..1, exp(-t u²)  (definitional)
    have h_boys0_rw : ∀ r₁ : ℝ³,
        boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) =
          ∫ u in (0:ℝ)..1, Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2) := by
      intro r₁; rfl
    -- (1) replace boys0 by the interval integral
    rw [show (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          boys0 (q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)) =
        (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          (∫ u in (0:ℝ)..1, Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2))) by
      refine integral_congr_ae ?_; filter_upwards with r₁; rw [h_boys0_rw r₁]]
    -- (2) interval integral ↔ set integral over Ioc 0 1
    rw [show (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          (∫ u in (0:ℝ)..1, Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2))) =
        (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          (∫ u in Ioc (0:ℝ) 1, Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2))) by
      refine integral_congr_ae ?_; filter_upwards with r₁
      rw [← intervalIntegral.integral_of_le h01]]
    -- (3) set integral ↔ whole-space indicator; pull exp(-pΣ) inside the u-integral.
    rw [show (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          (∫ u in Ioc (0:ℝ) 1, Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2))) =
        (∫ r₁ : ℝ³, ∫ u : ℝ, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          ((Ioc (0:ℝ) 1).indicator
            (fun u => Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2)) u)) by
      refine integral_congr_ae ?_; filter_upwards with r₁
      rw [← integral_indicator measurableSet_Ioc, ← integral_const_mul]]
    -- (4) integrability of the joint function, then Fubini.
    set F : ℝ³ × ℝ → ℝ := fun p_ => Real.exp (-p * ∑ i : Fin 3, (p_.1 i - P i) ^ 2) *
        ((Ioc (0:ℝ) 1).indicator
          (fun u => Real.exp (-(q * ∑ i : Fin 3, (p_.1 i - Q i) ^ 2) * u ^ 2)) p_.2) with hFdef
    have hF_int : Integrable F (volume.prod volume) := by
      set G : ℝ³ × ℝ → ℝ := fun p_ =>
        Real.exp (-p * ∑ i : Fin 3, (p_.1 i - P i) ^ 2) *
          ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) p_.2) with hGdef
      have hF_le_G : ∀ x, ‖F x‖ ≤ G x := by
        intro x
        have hFn : 0 ≤ F x := by
          simp only [F]
          by_cases hu : x.2 ∈ Ioc (0:ℝ) 1
          · rw [Set.indicator_of_mem hu]; positivity
          · rw [Set.indicator_of_notMem hu]; positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hFn]
        simp only [F, G]
        by_cases hu : x.2 ∈ Ioc (0:ℝ) 1
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          have h_qu_nn : 0 ≤ q * ∑ i, (x.1 i - Q i) ^ 2 := by
            refine mul_nonneg hq_pos.le ?_
            exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have h_prod_nn : 0 ≤ (q * ∑ i, (x.1 i - Q i) ^ 2) * x.2 ^ 2 :=
            mul_nonneg h_qu_nn (sq_nonneg _)
          have h_le1 : Real.exp (-((q * ∑ i, (x.1 i - Q i) ^ 2)) * x.2 ^ 2) ≤ 1 := by
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
          linarith
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      have hG_int : Integrable G (volume.prod volume) := by
        have hG_eq : G = fun p_ =>
            (fun r : ℝ³ => Real.exp (-p * ∑ i : Fin 3, (r i - P i) ^ 2)) p_.1 *
            ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) p_.2) := by rfl
        rw [hG_eq]
        have h_int_r : Integrable (fun r : ℝ³ => Real.exp (-p * ∑ i : Fin 3, (r i - P i) ^ 2))
            volume := by
          have h_each : Integrable (fun x : ℝ => Real.exp (-p * x ^ 2)) volume :=
            integrable_exp_neg_mul_sq hp_pos
          have h_prod_centered : Integrable
              (fun r : ℝ³ => ∏ i, Real.exp (-p * (r i - P i) ^ 2)) volume := by
            have h_base : Integrable (fun r : ℝ³ => ∏ i, Real.exp (-p * (r i) ^ 2)) volume :=
              Integrable.fintype_prod (μ := fun _ => volume) (fun _ => h_each)
            have h_eq : (fun r : ℝ³ => ∏ i, Real.exp (-p * (r i - P i) ^ 2)) =
                fun r : ℝ³ => ∏ i, Real.exp (-p * ((r - P) i) ^ 2) := by
              funext r; simp only [Pi.sub_apply]
            rw [h_eq]; exact h_base.comp_sub_right P
          convert h_prod_centered using 1
          funext r; rw [Finset.mul_sum, ← Real.exp_sum]
        have h_int_u : Integrable ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ))) volume := by
          have h_finite : volume (Ioc (0:ℝ) 1) < ⊤ := by
            rw [Real.volume_Ioc]; simp
          clear * -
          rw [integrable_indicator_iff] <;> simp
        --exact ⟨h_int_r, h_int_u⟩
        --clear * - h_int_r h_int_u
        --rw [integrable_prod]
        exact h_int_r.mul_prod h_int_u
      refine hG_int.mono' ?_ ?_
      · have hF_meas : Measurable F := by
          refine Measurable.mul ?_ ?_
          · fun_prop
          · refine Measurable.indicator ?_ (measurable_snd measurableSet_Ioc)
            fun_prop
        exact hF_meas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall hF_le_G
    have hF_eq : (Function.uncurry fun (r₁ : ℝ³) (u : ℝ) =>
        Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          ((Ioc (0:ℝ) 1).indicator
            (fun u => Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2)) u)) = F := by
      ext ⟨r₁, u⟩; rfl
    rw [show (∫ r₁ : ℝ³, ∫ u : ℝ, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          ((Ioc (0:ℝ) 1).indicator
            (fun u => Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2)) u)) =
        (∫ r₁ : ℝ³, ∫ u : ℝ, F (r₁, u)) by rfl, integral_integral_swap hF_int]
    -- (5) split off the indicator; combine the two exponentials.
    rw [show (∫ u : ℝ, ∫ r₁ : ℝ³, F (r₁, u)) =
        (∫ u : ℝ, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
          (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
            Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) by
      refine integral_congr_ae ?_; filter_upwards with u
      have h_ind (r₁ : ℝ³) : ((Ioc (0:ℝ) 1).indicator
            (fun u => Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2)) u) =
          ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
            Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) := by
        by_cases hu : u ∈ Ioc (0:ℝ) 1
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul]; congr 1; ring
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]; ring
      calc (∫ r₁ : ℝ³, F (r₁, u))
          = (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
              ((Ioc (0:ℝ) 1).indicator
                (fun u => Real.exp (-(q * ∑ i : Fin 3, (r₁ i - Q i) ^ 2) * u ^ 2)) u)) := rfl
        _ = (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
              (((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
                Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) := by
          refine integral_congr_ae ?_; filter_upwards with r₁; rw [h_ind r₁]
        _ = ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
              (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
                Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2)) := by
          rw [show (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
                (((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
                  Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) =
              (∫ r₁ : ℝ³, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
                (Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
                  Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) by
              refine integral_congr_ae ?_; filter_upwards with r₁; ring,
            integral_const_mul]]
    -- (6) combine the two exps into one.
    rw [show (∫ u : ℝ, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
          (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
            Real.exp (-(q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) =
        (∫ u : ℝ, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
          (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 -
            (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) by
      refine integral_congr_ae ?_; filter_upwards with u
      refine congr_arg _ ?_
      refine integral_congr_ae ?_; filter_upwards with r₁
      rw [← Real.exp_add]; ring_nf]
    -- (7) collapse the indicator back to a set integral over Ioc 0 1, then to an interval integral.
    rw [show (∫ u : ℝ, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
          (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 -
            (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) =
        (∫ u in Ioc (0:ℝ) 1, (∫ r₁ : ℝ³,
          Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 - (q * u ^ 2) * ∑ i : Fin 3,
            (r₁ i - Q i) ^ 2))) by
      rw [show (∫ u : ℝ, ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) u) *
            (∫ r₁ : ℝ³, Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 -
              (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) =
          (∫ u : ℝ, (Ioc (0:ℝ) 1).indicator
            (fun u => ∫ r₁ : ℝ³,
              Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 - (q * u ^ 2) * ∑ i : Fin 3,
                (r₁ i - Q i) ^ 2)) u) by
        refine integral_congr_ae ?_; filter_upwards with u
        by_cases hu : u ∈ Ioc (0:ℝ) 1 <;> simp [Set.indicator, hu],
        ← integral_indicator measurableSet_Ioc]]
    rw [intervalIntegral.integral_of_le h01]
  rw [h_swap]
  -- Step 5: shift r₁ by P, apply helper with γ=p, c=q*u², A=Q-P.
  have h_c_nn (u : ℝ) : 0 ≤ q * u ^ 2 := by
    refine mul_nonneg hq_pos.le ?_; exact sq_nonneg _
  rw [show (∫ u in (0:ℝ)..1, (∫ r₁ : ℝ³,
        Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2 -
          (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - Q i) ^ 2))) =
      (∫ u in (0:ℝ)..1, (∫ r₁ : ℝ³,
        Real.exp (-p * ∑ i : Fin 3, (r₁ i) ^ 2 -
          (q * u ^ 2) * ∑ i : Fin 3, (r₁ i - (Q - P) i) ^ 2))) by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have h_trans := integral_sub_right_eq_self (μ := (volume : Measure ℝ³))
      (fun r₁ : ℝ³ => Real.exp (-p * ∑ i, (r₁ i) ^ 2 -
        (q * u ^ 2) * ∑ i, (r₁ i - (Q - P) i) ^ 2)) P
    rw [← h_trans]
    refine integral_congr_ae ?_
    filter_upwards with r₁
    simp [Pi.sub_apply]]
  -- Apply the helper: γ=p, c=q*u², A=Q-P.
  have h_inner (u : ℝ) : (∫ r₁ : ℝ³,
      Real.exp (-p * ∑ i : Fin 3, (r₁ i) ^ 2 - (q * u ^ 2) * ∑ i, (r₁ i - (Q - P) i) ^ 2)) =
    (Real.sqrt (π / (p + q * u ^ 2))) ^ 3 *
      Real.exp (-(p * (q * u ^ 2)) / (p + q * u ^ 2) * ∑ i : Fin 3, ((Q - P) i) ^ 2) := by
    rw [integral_exp_combined_3d_nonneg p (q * u ^ 2) hp_pos (h_c_nn u) (Q - P)]
  simp_rw [h_inner]
  -- Step 6: outer u integral via integral_Icc_gaussian_to_boys0.
  -- Lemma with lemma's p := q, lemma's q := p, S := Σ(Q-P)², so the denominators match p+q*u².
  rw [show (∫ u in (0:ℝ)..1, (Real.sqrt (π / (p + q * u ^ 2))) ^ 3 *
        Real.exp (-(p * (q * u ^ 2)) / (p + q * u ^ 2) * ∑ i : Fin 3, ((Q - P) i) ^ 2)) =
      (∫ u in (0:ℝ)..1, (Real.sqrt (π / (p + q * u ^ 2))) ^ 3 *
        Real.exp (-(q * p * u ^ 2) / (p + q * u ^ 2) * ∑ i : Fin 3, ((Q - P) i) ^ 2)) by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    refine congr_arg (fun t => (Real.sqrt (π / (p + q * u ^ 2))) ^ 3 * Real.exp t) ?_
    field_simp
    try ring,
    integral_Icc_gaussian_to_boys0 q p (∑ i : Fin 3, ((Q - P) i) ^ 2) hq_pos hp_pos]
  -- Step 7: reconcile constants and the boys0 argument; unfold p,q,P,Q,K₁,K₂ to the target.
  have h_sqrt_pi_cube : (Real.sqrt π) ^ 3 = π ^ (3/2 : ℝ) := by
    have h1 : (Real.sqrt π) ^ 3 = ((Real.sqrt π) ^ 2) * Real.sqrt π := by ring
    rw [h1, Real.sq_sqrt (by positivity : 0 ≤ π)]
    have h_pi_1 : π ^ (1 : ℝ) = π := by simp
    rw [show (3/2 : ℝ) = 1 + (1/2 : ℝ) by norm_num, Real.rpow_add Real.pi_pos,
      Real.sqrt_eq_rpow, h_pi_1]
  have h_pi_5_2 : π ^ (5/2 : ℝ) = π * π ^ (3/2 : ℝ) := by
    rw [show (5/2 : ℝ) = 1 + (3/2 : ℝ) by norm_num, Real.rpow_add Real.pi_pos]
    simp
  rw [h_sqrt_pi_cube, h_pi_5_2]
  -- The boys0 argument: qp/(p+q) * Σ(Q-P)² = pq/(p+q) * Σ(P-Q)² with P,Q unfolded.
  have h_SPQ_symm : ∑ i : Fin 3, ((Q - P) i) ^ 2 =
      ∑ i : Fin 3, (((α₁ * R₁ i + α₂ * R₂ i) / (α₁ + α₂)) -
        ((α₃ * R₃ i + α₄ * R₄ i) / (α₃ + α₄))) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    dsimp only [P, Q, p, q]
    ring
  rw [h_SPQ_symm]
  dsimp only [K₁, K₂, p, q]
  have hpq_ne : α₁ + α₂ + (α₃ + α₄) ≠ 0 := by linarith
  have hq_inner_ne : α₃ + α₄ ≠ 0 := by linarith
  have hp_inner_ne : α₁ + α₂ ≠ 0 := by linarith
  -- Normalize the boys0-argument factor order and the √ argument to match the target exactly.
  rw [show (α₃ + α₄) * (α₁ + α₂) = (α₁ + α₂) * (α₃ + α₄) by ring,
      show (α₃ + α₄) + (α₁ + α₂) = (α₁ + α₂) + (α₃ + α₄) by ring]
  field_simp [hp_inner_ne, hq_inner_ne, hpq_ne]

/-! ## 12. Higher angular momentum: Coulomb moment auxiliaries and the Boys reduction

The s-type results above express the Coulomb integrals in terms of `boys0`. For general angular
momentum the Gaussian product theorem still localizes the bra/ket to a single Gaussian, but the
polynomial prefactor `∏ᵢ (rᵢ+Aᵢ)^lᵢ (rᵢ+Bᵢ)^mᵢ` survives. Expanding it by the binomial theorem
leaves a finite sum of **Coulomb moment integrals** — moments of a single Gaussian against the
Coulomb kernel — which reduce to the higher Boys functions `boys n`.

We isolate these moments as the auxiliaries `coulombMomentν` (one-electron) and `eriMomentν`
(two-electron). Their evaluation is governed by a base case (the s-type identity already proved
above) and the McMurchie–Davidson transfer recurrences, which raise a Cartesian moment by one unit
in a coordinate in exchange for a partial derivative of the moment with respect to the Coulomb
center. Iterating the recurrence expresses every moment as a derivative (in `D` or `W`) of the base
`boys0`, hence (via `boys_iteratedDeriv`) as a finite linear combination of `boys n`.

The statements below are asserted without proof; they are the scaffold for a future derivation.
Each main theorem specializes, at `l = m = 0`, to the corresponding s-type result of sections 9/11.
-/

/-- The one-electron Coulomb moment: the Gaussian-weighted integral of a monomial `∏ᵢ rᵢ^νᵢ`
against the Coulomb kernel `1/‖r - D‖`,
  `coulombMomentν ν γ D = ∫ ∏ᵢ rᵢ^νᵢ · exp(-γ·‖r‖²) · (1/‖r-D‖) dr`.
For `ν = 0` this is `integral_exp_neg_mul_sq_coulomb`, i.e. `(2π/γ)·boys0(γ·‖D‖²)`. -/
noncomputable def coulombMomentν (ν : Fin 3 → ℕ) (γ : ℝ) (D : ℝ³) : ℝ :=
  ∫ r : ℝ³, (∏ i : Fin 3, r i ^ ν i) * Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) * coulomb r D

/-- The two-electron Coulomb moment: moments of two Gaussians (exponents `p`, `q`) against the
Coulomb kernel `1/‖r₁ - r₂ + W‖` (with `W = P - Q` the separation of the two product centers),
  `eriMomentν ν μ p q W =
    ∫∫ ∏ᵢ r₁ᵢ^νᵢ · ∏ᵢ r₂ᵢ^μᵢ · exp(-p·‖r₁‖² - q·‖r₂‖²) · (1/‖r₁ - r₂ + W‖) dr₁ dr₂`.
For `ν = μ = 0` this is the s-type ERI auxiliary, i.e.
`(2π^(5/2))/(p·q·√(p+q))·boys0(pq/(p+q)·‖W‖²)`. -/
noncomputable def eriMomentν (ν μ : Fin 3 → ℕ) (p q : ℝ) (W : ℝ³) : ℝ :=
  ∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
    (∏ i : Fin 3, r₁ i ^ ν i) * (∏ i : Fin 3, r₂ i ^ μ i) *
      Real.exp (-p * ∑ i : Fin 3, (r₁ i) ^ 2) * Real.exp (-q * ∑ i : Fin 3, (r₂ i) ^ 2) *
      coulomb r₁ (r₂ - W)

/-- Base case of the Coulomb moment: the s-type (zero-moment) identity `integral_exp_neg_mul_sq_coulomb`. -/
lemma coulombMomentν_zero (γ : ℝ) (hγ : 0 < γ) (D : ℝ³) :
    coulombMomentν 0 γ D = (2 * π / γ) * boys0 (γ * ∑ i : Fin 3, (D i) ^ 2) := by sorry

/-- McMurchie–Davidson transfer recurrence (one-electron). Raising the `i`-th Cartesian moment by
one costs a `Dᵢ`-derivative of the lower moment (from `rᵢ·exp(-γ‖r‖²) = -(2γ)⁻¹·∂_{rᵢ}exp(-γ‖r‖²)`
and integration by parts, using `∂_{rᵢ} coulomb(r,D) = -∂_{Dᵢ} coulomb(r,D)`), plus a
`(νᵢ/(2γ))·coulombMomentν(ν-eᵢ)` term from differentiating the polynomial prefactor. -/
lemma coulombMomentν_succ (ν : Fin 3 → ℕ) (γ : ℝ) (hγ : 0 < γ) (i : Fin 3) (D : ℝ³) :
    coulombMomentν (Function.update ν i (ν i + 1)) γ D =
      (ν i : ℝ) / (2 * γ) * coulombMomentν (Function.update ν i (ν i - 1)) γ D
        - (1 / (2 * γ))
            * deriv (fun x => coulombMomentν ν γ (Function.update D i x)) (D i) := by sorry

/-- Base case of the two-electron Coulomb moment: the s-type ERI auxiliary. -/
lemma eriMomentν_zero (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (W : ℝ³) :
    eriMomentν 0 0 p q W =
      (2 * π ^ (5/2 : ℝ)) / (p * q * Real.sqrt (p + q))
        * boys0 (p * q / (p + q) * ∑ i : Fin 3, (W i) ^ 2) := by sorry

/-- Transfer recurrence for the `r₁`-moment (electron 1), with sign `+1/(2p)` on the derivative
(since `∂_{r₁ᵢ} coulomb(r₁,r₂-W) = ∂_{Wᵢ} coulomb(r₁,r₂-W)`). -/
lemma eriMomentν_succ_left (ν μ : Fin 3 → ℕ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (i : Fin 3) (W : ℝ³) :
    eriMomentν (Function.update ν i (ν i + 1)) μ p q W =
      (ν i : ℝ) / (2 * p) * eriMomentν (Function.update ν i (ν i - 1)) μ p q W
        + (1 / (2 * p))
            * deriv (fun x => eriMomentν ν μ p q (Function.update W i x)) (W i) := by sorry

/-- Transfer recurrence for the `r₂`-moment (electron 2), with sign `-1/(2q)` on the derivative
(since `∂_{r₂ᵢ} coulomb(r₁,r₂-W) = -∂_{Wᵢ} coulomb(r₁,r₂-W)`). -/
lemma eriMomentν_succ_right (ν μ : Fin 3 → ℕ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (i : Fin 3) (W : ℝ³) :
    eriMomentν ν (Function.update μ i (μ i + 1)) p q W =
      (μ i : ℝ) / (2 * q) * eriMomentν ν (Function.update μ i (μ i - 1)) p q W
        - (1 / (2 * q))
            * deriv (fun x => eriMomentν ν μ p q (Function.update W i x)) (W i) := by sorry

/-- Closed form of the nuclear-attraction integral for two primitive GTOs of general angular
momentum. The Gaussian product theorem localizes the product to the center `P =
gaussianProductCenter α β R₁ R₂`; translating `r ↦ r + P` and binomial-expanding the surviving
polynomial leaves a finite sum of Coulomb moments `coulombMomentν` at the shifted nucleus
`D = C - P`, with prefactor `K = exp(-αβ/(α+β)·‖R₁-R₂‖²)`. At `l = m = 0` the sum collapses to the
single base moment and this reproduces `nuclearAttraction_primitiveGTO_s`. -/
theorem nuclearAttraction_primitiveGTO (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (R₁ R₂ C : ℝ³) (l m : Fin 3 → ℕ) :
    let P : ℝ³ := gaussianProductCenter α β R₁ R₂
    let γ : ℝ := α + β
    nuclearAttraction C (primitiveGTO α R₁ l) (primitiveGTO β R₂ m) =
      Real.exp (-(α * β) / γ * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        (∑ a ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (l i + 1)),
          ∑ b ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (m i + 1)),
            (∏ i : Fin 3,
              ((l i).choose (a i) : ℝ) * ((m i).choose (b i) : ℝ) *
                (P i - R₁ i) ^ (l i - a i) * (P i - R₂ i) ^ (m i - b i)) *
              coulombMomentν (fun i : Fin 3 => a i + b i) γ (C - P)) := by
  sorry

/-- Closed form of the two-electron repulsion integral for four primitive GTOs of general angular
momentum. Both bra and ket are localized by the Gaussian product theorem (centers `P`, `Q`), the
surviving polynomials binomial-expand into a finite sum of two-electron Coulomb moments
`eriMomentν` at separation `W = P - Q`, with prefactors `K₁·K₂`. At zero angular momentum the sum
collapses to the base moment and this reproduces `electronRepulsion_primitiveGTO_s`. -/
theorem electronRepulsion_primitiveGTO (α₁ α₂ α₃ α₄ : ℝ)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα₃ : 0 < α₃) (hα₄ : 0 < α₄)
    (R₁ R₂ R₃ R₄ : ℝ³) (l₁ l₂ l₃ l₄ : Fin 3 → ℕ) :
    let P : ℝ³ := gaussianProductCenter α₁ α₂ R₁ R₂
    let Q : ℝ³ := gaussianProductCenter α₃ α₄ R₃ R₄
    let pp : ℝ := α₁ + α₂
    let qq : ℝ := α₃ + α₄
    electronRepulsion (primitiveGTO α₁ R₁ l₁) (primitiveGTO α₂ R₂ l₂)
        (primitiveGTO α₃ R₃ l₃) (primitiveGTO α₄ R₄ l₄) =
      Real.exp (-(α₁ * α₂) / pp * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        Real.exp (-(α₃ * α₄) / qq * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) *
        (∑ a ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (l₁ i + 1)),
          ∑ b ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (l₂ i + 1)),
            ∑ c ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (l₃ i + 1)),
              ∑ d ∈ Fintype.piFinset (fun i : Fin 3 => Finset.range (l₄ i + 1)),
                (∏ i : Fin 3,
                  ((l₁ i).choose (a i) : ℝ) * ((l₂ i).choose (b i) : ℝ) *
                    ((l₃ i).choose (c i) : ℝ) * ((l₄ i).choose (d i) : ℝ) *
                    (P i - R₁ i) ^ (l₁ i - a i) * (Q i - R₃ i) ^ (l₃ i - c i) *
                    (P i - R₂ i) ^ (l₂ i - b i) * (Q i - R₄ i) ^ (l₄ i - d i)) *
                  eriMomentν (fun i : Fin 3 => a i + b i) (fun i : Fin 3 => c i + d i) pp qq (P - Q)) := by
  sorry

end GTO
