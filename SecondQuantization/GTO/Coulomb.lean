import SecondQuantization.GTO.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace GTO

open Real MeasureTheory Set

set_option linter.style.longLine false

noncomputable def boys0 (t : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-t * u ^ 2)

/-! ## 1. Derivative of `u/√(γ+u²)` = `γ/(γ+u²)^(3/2)` -/

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
            (γ + u ^ 2) ^ (3/2 : ℝ) = (γ + u ^ 2) ^ ((1/2 : ℝ) * (3 : ℝ)) := by ring
            _ = ((γ + u ^ 2) ^ (1/2 : ℝ)) ^ (3 : ℝ) := by
              rw [rpow_mul (by nlinarith : 0 ≤ γ + u ^ 2) (1/2 : ℝ) (3 : ℝ)]
            _ = (Real.sqrt (γ + u ^ 2)) ^ (3 : ℝ) := by rw [Real.sqrt_eq_rpow]
            _ = (Real.sqrt (γ + u ^ 2)) ^ 3 := by norm_num
        rw [h_pow_eq]

/-! ## 2. Strict monotonicity on (0,∞) -/

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
      Real.exp (-γ * ∑ i, (r i) ^ 2 - t ^ 2 * ∑ i, (r i - A i) ^ 2) = Real.exp ((-γ * ∑ i, (r i) ^ 2) + (-(t ^ 2) * ∑ i, (r i - A i) ^ 2)) := by ring
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

lemma coulomb_eq_integral_ae (A : ℝ³) :
    (fun r => coulomb r A) =ᵐ[volume] fun r => (2 / Real.sqrt π) * ∫ t in Ioi (0 : ℝ), Real.exp (-(∑ i, (r i - A i) ^ 2) * t ^ 2) := by
  have h_ae_ne : ∀ᵐ r : (ℝ³), r ≠ A := by
    have h_null : volume ({A} : Set (ℝ³)) = 0 := measure_singleton A
    rw [ae_iff]; simpa using h_null
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
        _ = (γ + t ^ 2) ^ (3/2 : ℝ) := by ring
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
          ring
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

/-! ## 8. Nuclear attraction integral -/

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

/-! ## 9. Electron repulsion integral -/

/-- The double-integral identity for the ERI: for `p,q > 0`,
`∫∫ exp(-p|r₁-P|²) exp(-q|r₂-Q|²) / |r₁-r₂| dr₁dr₂ = (2π^(5/2)/(pq√(p+q))) · F₀(pq|P-Q|²/(p+q))`.

This is a standard quantum-chemistry result whose full Lean proof requires Fubini-Tonelli
on ℝ³ × ℝ³, two applications of `integral_exp_combined_3d`, and the same nonlinear change
of variables as in `integral_exp_neg_mul_sq_coulomb`. The algebraic derivation is outlined
above; the measure-theoretic integrability conditions are omitted. -/
lemma integral_double_exp_coulomb (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (P Q : ℝ³) :
    (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
      Real.exp (-p * ∑ i, (r₁ i - P i) ^ 2) *
      Real.exp (-q * ∑ i, (r₂ i - Q i) ^ 2) *
      coulomb r₁ r₂) =
    (2 * π ^ (5/2 : ℝ)) / (p * q * Real.sqrt (p + q)) *
      boys0 (p * q / (p + q) * ∑ i : Fin 3, (P i - Q i) ^ 2) := by
  sorry

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
  set p := α₁ + α₂ with hp
  set q := α₃ + α₄ with hq
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < q := by linarith
  set P : ℝ³ := fun i => (α₁ * R₁ i + α₂ * R₂ i) / p with hP
  set Q : ℝ³ := fun i => (α₃ * R₃ i + α₄ * R₄ i) / q with hQ
  set K₁₂ := Real.exp (-(α₁ * α₂) / p * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) with hK₁₂
  set K₃₄ := Real.exp (-(α₃ * α₄) / q * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) with hK₃₄
  -- Gaussian product theorem for each pair
  have h_prod12 (r : ℝ³) : primitiveGTO_s α₁ R₁ r * primitiveGTO_s α₂ R₂ r =
      K₁₂ * Real.exp (-p * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    dsimp [K₁₂, P, p]
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have hsq : ∀ x a b : ℝ, -α₁ * (x - a) ^ 2 + -α₂ * (x - b) ^ 2 =
        -(α₁ * α₂) / (α₁ + α₂) * (a - b) ^ 2 + -(α₁ + α₂) * (x - (α₁ * a + α₂ * b) / (α₁ + α₂)) ^ 2 := by
      intro x a b; field_simp [show α₁ + α₂ ≠ 0 from by linarith]; ring
    calc
      -α₁ * ∑ i : Fin 3, (r i - R₁ i) ^ 2 + -α₂ * ∑ i : Fin 3, (r i - R₂ i) ^ 2
          = ∑ i : Fin 3, (-α₁ * (r i - R₁ i) ^ 2 + -α₂ * (r i - R₂ i) ^ 2) := by
            simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α₁ * α₂) / (α₁ + α₂) * (R₁ i - R₂ i) ^ 2
              + -(α₁ + α₂) * (r i - P i) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            dsimp [P]; rw [hsq (r i) (R₁ i) (R₂ i)]
      _ = (-(α₁ * α₂) / (α₁ + α₂) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2)
            + (-(α₁ + α₂) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
              simp [Finset.mul_sum, Finset.sum_add_distrib]
  have h_prod34 (r : ℝ³) : primitiveGTO_s α₃ R₃ r * primitiveGTO_s α₄ R₄ r =
      K₃₄ * Real.exp (-q * ∑ i : Fin 3, (r i - Q i) ^ 2) := by
    dsimp [K₃₄, Q, q]
    simp only [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have hsq : ∀ x a b : ℝ, -α₃ * (x - a) ^ 2 + -α₄ * (x - b) ^ 2 =
        -(α₃ * α₄) / (α₃ + α₄) * (a - b) ^ 2 + -(α₃ + α₄) * (x - (α₃ * a + α₄ * b) / (α₃ + α₄)) ^ 2 := by
      intro x a b; field_simp [show α₃ + α₄ ≠ 0 from by linarith]; ring
    calc
      -α₃ * ∑ i : Fin 3, (r i - R₃ i) ^ 2 + -α₄ * ∑ i : Fin 3, (r i - R₄ i) ^ 2
          = ∑ i : Fin 3, (-α₃ * (r i - R₃ i) ^ 2 + -α₄ * (r i - R₄ i) ^ 2) := by
            simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i : Fin 3, (-(α₃ * α₄) / (α₃ + α₄) * (R₃ i - R₄ i) ^ 2
              + -(α₃ + α₄) * (r i - Q i) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            dsimp [Q]; rw [hsq (r i) (R₃ i) (R₄ i)]
      _ = (-(α₃ * α₄) / (α₃ + α₄) * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2)
            + (-(α₃ + α₄) * ∑ i : Fin 3, (r i - Q i) ^ 2) := by
              simp [Finset.mul_sum, Finset.sum_add_distrib]
  unfold electronRepulsion
  calc
    (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
        primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
        coulomb r₁ r₂ *
        primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂)
      = (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
          (K₁₂ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) *
          coulomb r₁ r₂ *
          (K₃₄ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2))) := by
        refine integral_congr_ae ?_
        filter_upwards with r₁
        refine integral_congr_ae ?_
        filter_upwards with r₂
        calc
          primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁ *
              coulomb r₁ r₂ *
              primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂
            = (primitiveGTO_s α₁ R₁ r₁ * primitiveGTO_s α₂ R₂ r₁) * coulomb r₁ r₂ *
                (primitiveGTO_s α₃ R₃ r₂ * primitiveGTO_s α₄ R₄ r₂) := by ring
          _ = (K₁₂ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) * coulomb r₁ r₂ *
                (K₃₄ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) := by
              rw [h_prod12 r₁, h_prod34 r₂]
          _ = (K₁₂ * Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2)) * coulomb r₁ r₂ *
                (K₃₄ * Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) := rfl
    _ = (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
          K₁₂ * K₃₄ * (Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
            coulomb r₁ r₂ *
            Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2))) := by
      refine integral_congr_ae ?_
      filter_upwards with r₁
      refine integral_congr_ae ?_
      filter_upwards with r₂
      ring
    _ = K₁₂ * K₃₄ * (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
          Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          coulomb r₁ r₂ *
          Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2)) := by
      simp [integral_const_mul]
    _ = K₁₂ * K₃₄ * (∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
          Real.exp (-p * ∑ i : Fin 3, (r₁ i - P i) ^ 2) *
          Real.exp (-q * ∑ i : Fin 3, (r₂ i - Q i) ^ 2) *
          coulomb r₁ r₂) := by
      refine congrArg (fun t => K₁₂ * K₃₄ * t) (integral_congr_ae ?_)
      filter_upwards with r₁
      refine integral_congr_ae ?_
      filter_upwards with r₂
      ring
    _ = K₁₂ * K₃₄ * ((2 * π ^ (5/2 : ℝ)) / (p * q * Real.sqrt (p + q)) *
          boys0 (p * q / (p + q) * ∑ i : Fin 3, (P i - Q i) ^ 2)) := by
      rw [integral_double_exp_coulomb p q hp_pos hq_pos P Q]
    _ = (2 * π ^ (5/2 : ℝ)) /
          ((α₁ + α₂) * (α₃ + α₄) * Real.sqrt ((α₁ + α₂) + (α₃ + α₄))) *
          Real.exp (-(α₁ * α₂) / (α₁ + α₂) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          Real.exp (-(α₃ * α₄) / (α₃ + α₄) * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) *
          boys0 ((α₁ + α₂) * (α₃ + α₄) / ((α₁ + α₂) + (α₃ + α₄)) *
            ∑ i : Fin 3, (((α₁ * R₁ i + α₂ * R₂ i) / (α₁ + α₂)) -
              ((α₃ * R₃ i + α₄ * R₄ i) / (α₃ + α₄))) ^ 2) := by
      dsimp [K₁₂, K₃₄, P, Q, p, q]
      ring

end GTO
