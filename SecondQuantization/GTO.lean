import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-!

# Gaussian Type Orbitals

This file formalizes the Cartesian Gaussian Type Orbitals (GTO), which are the standard atomic
basis functions used in quantum chemistry. A primitive Cartesian GTO centered at `R ∈ ℝ³` with
exponent `α > 0` and angular momentum `(lx, ly, lz) : Fin 3 → ℕ` is the function

  φ(r) = (x - Rx)^lx · (y - Ry)^ly · (z - Rz)^lz · exp (-α · ‖r - R‖²)

A contracted GTO is a finite linear combination of primitive GTOs that share the same center and
angular momentum but have different exponents and coefficients.

## Definitions

* `primitiveGTO` — a primitive Cartesian Gaussian centered at `R` with exponent `α` and angular
  momentum `l`.
* `contractedGTO` — a contracted Gaussian: finite sum of primitives with shared center / angular
  momentum.
* `overlap` — the overlap integral `∫ φ(r) ψ(r) dr` between two GTOs.
* `nuclearAttraction` — the one-electron nuclear attraction integral `∫ φ(r) (1/‖r - C‖) ψ(r) dr`.
* `electronRepulsion` — the two-electron repulsion integral
  `∫∫ φ₁(r₁) φ₂(r₁) (1/‖r₁ - r₂‖) φ₃(r₂) φ₄(r₂) dr₁ dr₂`.
* `kinetic` — the kinetic energy integral `-½ ∫ φ(r) (∇² ψ)(r) dr`.

-/

namespace GTO

notation (name := R3) "ℝ³" => Fin 3 → ℝ

open Real MeasureTheory

/-- A primitive Cartesian Gaussian Type Orbital with center `R`, exponent `α` and
angular momentum quantum numbers `l : Fin 3 → ℕ`:
  `φ(r) = ∏ᵢ (rᵢ - Rᵢ)^lᵢ · exp (-α · ‖r - R‖²)`. -/
noncomputable def primitiveGTO (α : ℝ) (R : ℝ³) (l : Fin 3 → ℕ) : ℝ³ → ℝ :=
  fun r ↦ (∏ i : Fin 3, (r i - R i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2)

/-- An s-type primitive GTO has zero angular momentum. -/
noncomputable abbrev primitiveGTO_s (α : ℝ) (R : ℝ³) : ℝ³ → ℝ :=
  primitiveGTO α R 0

/-- A contracted GTO: a finite linear combination of primitive GTOs sharing the same center `R`
and angular momentum `l`, parameterized by an index type `ι` with coefficients `c i` and exponents
`α i`. -/
noncomputable def contractedGTO {ι : Type} [Fintype ι]
    (c : ι → ℝ) (α : ι → ℝ) (R : ℝ³) (l : Fin 3 → ℕ) : ℝ³ → ℝ :=
  fun r ↦ ∑ i : ι, c i * primitiveGTO (α i) R l r

/-- The overlap integral between two basis functions:
  `S = ∫ φ(r) · ψ(r) dr` over `ℝ³`. -/
noncomputable def overlap (φ ψ : ℝ³ → ℝ) : ℝ :=
  ∫ r : ℝ³, φ r * ψ r

/-- The nuclear attraction integral for a nucleus at `C`:
  `V = ∫ φ(r) · (1 / ‖r - C‖) · ψ(r) dr` over `ℝ³`. -/
noncomputable def nuclearAttraction (C : ℝ³) (φ ψ : ℝ³ → ℝ) : ℝ :=
  ∫ r : ℝ³, φ r * (1 / ‖(r - C : ℝ³)‖) * ψ r

/-- The two-electron repulsion integral (electron-electron interaction):
  `(φ₁ φ₂ | φ₃ φ₄) = ∫∫ φ₁(r₁) · φ₂(r₁) · (1 / ‖r₁ - r₂‖) · φ₃(r₂) · φ₄(r₂) dr₁ dr₂`. -/
noncomputable def electronRepulsion (φ₁ φ₂ φ₃ φ₄ : ℝ³ → ℝ) : ℝ :=
  ∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
    φ₁ r₁ * φ₂ r₁ * (1 / ‖(r₁ - r₂ : ℝ³)‖) * φ₃ r₂ * φ₄ r₂

/-- The kinetic energy integral:
  `T = ½ ∫ ∇φ(r) · ∇ψ(r) dr` over `ℝ³`.

This is equivalent to `-½ ∫ φ·(Δ ψ)` by integration by parts for Schwartz functions. -/
noncomputable def kinetic (φ ψ : ℝ³ → ℝ) : ℝ :=
  (1/2) * ∫ r : ℝ³,
    ∑ i : Fin 3, (fderiv ℝ φ r (Pi.single i 1)) * (fderiv ℝ ψ r (Pi.single i 1))

/-- The one-electron core Hamiltonian matrix element for nuclei `{(Z_k, C_k) : k}`:
  `h = T + ∑ₖ -Zₖ · ⟨φ | 1/‖r - Cₖ‖ | ψ⟩`. -/
noncomputable def coreHamiltonian {ι : Type} [Fintype ι]
    (Z : ι → ℝ) (C : ι → ℝ³) (φ ψ : ℝ³ → ℝ) : ℝ :=
  kinetic φ ψ + ∑ k : ι, (- Z k) * nuclearAttraction (C k) φ ψ

/-! ## Symmetry lemmas -/

/-- The overlap integral is symmetric in its two arguments. -/
theorem overlap_comm (φ ψ : ℝ³ → ℝ) : overlap φ ψ = overlap ψ φ := by
  unfold overlap
  simp_rw [mul_comm]

/-- The nuclear attraction integral is symmetric in `φ` and `ψ`. -/
theorem nuclearAttraction_comm (C : ℝ³) (φ ψ : ℝ³ → ℝ) :
    nuclearAttraction C φ ψ = nuclearAttraction C ψ φ := by
  unfold nuclearAttraction
  congr 1
  funext r
  ring

/-- The electron repulsion integral is symmetric in `φ₁` and `φ₂`. -/
theorem electronRepulsion_swap_12 (φ₁ φ₂ φ₃ φ₄ : ℝ³ → ℝ) :
    electronRepulsion φ₁ φ₂ φ₃ φ₄ = electronRepulsion φ₂ φ₁ φ₃ φ₄ := by
  unfold electronRepulsion
  congr 1
  funext r₁
  congr 1
  funext r₂
  ring

/-- The electron repulsion integral is symmetric in `φ₃` and `φ₄`. -/
theorem electronRepulsion_swap_34 (φ₁ φ₂ φ₃ φ₄ : ℝ³ → ℝ) :
    electronRepulsion φ₁ φ₂ φ₃ φ₄ = electronRepulsion φ₁ φ₂ φ₄ φ₃ := by
  unfold electronRepulsion
  congr 1
  funext r₁
  congr 1
  funext r₂
  ring

/-! ## Helper lemmas -/

/-- Completing the square for the Gaussian product theorem:
  `-α(x-a)² - β(x-b)² = -αβ/(α+β)·(a-b)² - (α+β)·(x - (αa+βb)/(α+β))²`.
  Requires `α + β ≠ 0` to avoid division by zero. -/
lemma complete_square (α β x a b : ℝ) (hαβ : α + β ≠ 0) :
    -α * (x - a) ^ 2 + -β * (x - b) ^ 2 =
      -(α * β) / (α + β) * (a - b) ^ 2
        + -(α + β) * (x - (α * a + β * b) / (α + β)) ^ 2 := by
  field_simp [hαβ]
  ring

/-- `exp(-γ·∑ᵢ rᵢ²) = ∏ᵢ exp(-γ·rᵢ²)`. Splits an exponential of a sum of squares
into a product of one-dimensional Gaussians. -/
lemma exp_neg_mul_sq_sum_eq_prod (γ : ℝ) (r : ℝ³) :
    Real.exp (-γ * ∑ i : Fin 3, (r i) ^ 2) =
      ∏ i : Fin 3, Real.exp (-γ * (r i) ^ 2) := by
  rw [Finset.mul_sum, ← Real.exp_sum]

/-- Translation invariance of the Lebesgue integral over `ℝ³`:
  `∫ f(r - R) dr = ∫ f(r) dr`. -/
lemma integral_translate (f : ℝ³ → ℝ) (R : ℝ³) :
    (∫ r : ℝ³, f (fun i => r i - R i)) = (∫ r : ℝ³, f r) := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ³)) f R
  simpa [Pi.sub_apply] using h

/-! ## Explicit integral evaluations -/

/-- The overlap of two s-type primitive GTOs sharing the same center is
  `∫ exp(-α‖r-R‖²) · exp(-β‖r-R‖²) dr = (√(π / (α + β)))^3`. -/
theorem overlap_primitiveGTO_s_same_center (α β : ℝ) (R : ℝ³) :
    overlap (primitiveGTO_s α R) (primitiveGTO_s β R) =
      (Real.sqrt (π / (α + β))) ^ 3 := by
  -- Reduce integrand to exp(-(α+β)·|r-R|²), then translate R→0 and factor
  have hsimp : ∀ r : ℝ³,
      primitiveGTO_s α R r * primitiveGTO_s β R r =
        Real.exp (-(α + β) * ∑ i : Fin 3, (r i - R i) ^ 2) := by
    intro r
    simp [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one]
    rw [← Real.exp_add]; congr 1; ring
  unfold overlap
  conv_lhs => arg 2; intro r; rw [hsimp r]
  rw [integral_translate (fun r => Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2)) R]
  simp_rw [exp_neg_mul_sq_sum_eq_prod (α + β)]
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
  -- Gaussian product center P = (α·R₁ + β·R₂) / (α+β)
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / (α + β) with hP
  -- Completing the square lifted to ℝ³ (the Gaussian product theorem)
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
      rw [show P i = (α * R₁ i + β * R₂ i) / (α + β) from rfl]
      exact complete_square α β (r i) (R₁ i) (R₂ i) hαβ
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
  -- Factor integrand: exp(-αβ/(α+β)·‖R₁-R₂‖²) · exp(-(α+β)·∑(r-P)²)
  have hsimp : ∀ r : ℝ³,
      primitiveGTO_s α R₁ r * primitiveGTO_s β R₂ r =
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
          Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2) := by
    intro r
    simp [primitiveGTO_s, primitiveGTO, Pi.zero_apply, pow_zero, Finset.prod_const_one]
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; simpa using h_exp_sum_eq r
  unfold overlap
  conv_lhs => arg 2; intro r; rw [hsimp r]
  rw [MeasureTheory.integral_const_mul]
  -- Translate P → 0, then factor and apply 1D Gaussian integral
  rw [integral_translate (fun r => Real.exp (-(α + β) * ∑ i : Fin 3, (r i) ^ 2)) P]
  simp_rw [exp_neg_mul_sq_sum_eq_prod (α + β)]
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

/-! ## Higher angular momentum, kinetic, nuclear attraction, ERI

The closed forms below are the standard quantum-chemistry results. Each requires either a
moment-integral lemma (the `(2k-1)!! / (2γ)^k · √(π/γ)` formula, not yet in Mathlib) or a
computation of the Laplacian of a Gaussian, or the Boys function. We state the formulas here
without proof, so the file documents the intended targets. -/

/-- The one-dimensional Gaussian even-moment formula:
  `M(2k, γ) = (2k-1)!! · √(π/γ) / (2γ)^k`. Odd moments vanish by symmetry. -/
noncomputable def gaussianMoment (n : ℕ) (γ : ℝ) : ℝ :=
  if n % 2 = 1 then 0
  else (Nat.doubleFactorial (n - 1) : ℝ) * Real.sqrt (π / γ) / (2 * γ) ^ (n / 2)

/-- **Target lemma.** The 1D Gaussian moment integral equals `gaussianMoment n γ` for `γ > 0`.
  Standard formula: `∫ x^n·exp(-γx²) dx = (n-1)‼·√(π/γ)/(2γ)^(n/2)` for even n, 0 for odd n.
  Proof outline: induction on `n` using integration by parts
  (`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`). -/
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
    · have hm2 : (m + 2) % 2 = 1 := by rw [Nat.add_mod_right]; simpa using hm
      simp [hm, hm2]
    · have hm_even : m % 2 = 0 := Nat.mod_two_eq_zero_or_one m |>.resolve_right hm
      have hm2_even : (m + 2) % 2 = 0 := by rw [Nat.add_mod_right]; simpa using hm_even
      simp [hm_even, hm2_even, Nat.doubleFactorial_add_one m, pow_succ]
      field_simp [show 2 * γ ≠ 0 by linarith]
  -- Integral recurrence: I_{m+2} = ((m+1)/(2γ)) * I_m, using derivative method
  have h_int_recurrence (m : ℕ) : (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
      ((m + 1 : ℝ) / (2 * γ)) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by
    set f := fun x : ℝ => x ^ (m + 1) * Real.exp (-γ * x ^ 2) with hf_def
    set f1 := fun x : ℝ => ((m + 1 : ℝ) * x ^ m * Real.exp (-γ * x ^ 2)) with hf1_def
    set f2 := fun x : ℝ => (2 * γ) * x ^ (m + 2) * Real.exp (-γ * x ^ 2) with hf2_def
    set f' := fun x : ℝ => f1 x - f2 x with hf'_def
    -- Derivative: f' = d/dx f = d/dx [x^(m+1)·exp(-γx²)]
    have h_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => x ^ (m + 1)) ((m + 1 : ℝ) * x ^ m) x := by
        simpa using hasDerivAt_pow (m + 1) x
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-γ * x ^ 2))
          (-2 * γ * x * Real.exp (-γ * x ^ 2)) x := by
        have h_inner : HasDerivAt (fun x : ℝ => -γ * x ^ 2) (-2 * γ * x) x := by
          simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using ((hasDerivAt_pow 2 x).const_mul (-γ))
        simpa [mul_comm] using (Real.hasDerivAt_exp (-γ * x ^ 2)).comp x h_inner
      dsimp [f, f1, f2, f']
      have h_mul := h1.mul h2
      dsimp [f, f1, f2, f']
      convert h_mul using 1
      ring
      dsimp [f1]; simpa [mul_assoc] using (h_int m).const_mul (m + 1 : ℝ)
    have h_int_f2 : Integrable f2 volume := by
      dsimp [f2]; simpa [mul_assoc] using (h_int (m + 2)).const_mul (2 * γ)
    have h_int_f' : Integrable f' volume := Integrable.sub h_int_f1 h_int_f2
    -- ∫ f' = 0 by fundamental theorem of calculus (boundary terms vanish at ±∞)
    have h_zero : (∫ x : ℝ, f' x) = 0 :=
      MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable h_deriv h_int_f' h_int_f
    -- Expand: ∫ f' = (m+1)*I_m - (2γ)*I_{m+2}
    have h_expanded : (∫ x : ℝ, f' x) = (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) -
        (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by
      dsimp [f', f1, f2]
      rw [integral_sub h_int_f1 h_int_f2]
      simp [integral_const_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [h_expanded] at h_zero
    -- Rearrange: (2γ)*I_{m+2} = (m+1)*I_m → I_{m+2} = (m+1)/(2γ) * I_m
    have h_eq : (2 * γ) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) =
        (m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) := by linarith
    have h_denom : 2 * γ ≠ 0 := by linarith
    calc
      (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2))
          = ((2 * γ)⁻¹ * (2 * γ)) * (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2)) := by
            field_simp [h_denom]
      _ = (2 * γ)⁻¹ * ((m + 1 : ℝ) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2))) := by
            rw [← h_eq]; ring
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
    have h_neg_pow (x : ℝ) : (-x) ^ n = -(x ^ n) := by
      have h_odd : Odd n := Nat.odd_iff.mpr hn_odd
      simpa using h_odd.neg_pow x
    have h_main : (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) =
        - (∫ x : ℝ, x ^ n * Real.exp (-γ * x ^ 2)) := by
      calc
        (∫ x, x ^ n * Real.exp (-γ * x ^ 2))
            = (∫ x, (-x) ^ n * Real.exp (-γ * (-x) ^ 2)) := by
              rw [integral_neg_eq_self (fun x => x ^ n * Real.exp (-γ * x ^ 2)) volume]
        _ = (∫ x, (-x) ^ n * Real.exp (-γ * x ^ 2)) := by
              refine integral_congr_ae ?_; filter_upwards with x; simp
        _ = (∫ x, (-(x ^ n)) * Real.exp (-γ * x ^ 2)) :=
              integral_congr_ae (by filter_upwards with x; simp [h_neg_pow])
        _ = - (∫ x, x ^ n * Real.exp (-γ * x ^ 2)) := by simp [integral_neg]
    linarith
  · -- Even n: handle n=0 directly, or use recurrence for n ≥ 2
    have hn_even : n % 2 = 0 := Nat.mod_two_eq_zero_or_one n |>.resolve_right hn_odd
    by_cases hn0 : n = 0
    · subst hn0
      simp [gaussianMoment, neg_mul, integral_gaussian γ]
    by_cases hn1 : n = 1
    · subst hn1; norm_num at hn_even
    -- n ≥ 2: write n = m + 2, apply recurrence and induction hypothesis
    have hn_ge2 : 2 ≤ n := by omega
    rcases Nat.exists_eq_add_of_le hn_ge2 with ⟨m, hm⟩
    rw [show n = m + 2 by omega] at ih ⊢
    calc
      (∫ x : ℝ, x ^ (m + 2) * Real.exp (-γ * x ^ 2))
          = ((m + 1 : ℝ) / (2 * γ)) * (∫ x : ℝ, x ^ m * Real.exp (-γ * x ^ 2)) :=
        h_int_recurrence m
      _ = ((m + 1 : ℝ) / (2 * γ)) * gaussianMoment m γ := by rw [ih m (by omega)]
      _ = gaussianMoment (m + 2) γ := by rw [h_gm_recurrence m]

/-- The overlap of two same-center primitive GTOs with general angular momenta `l`, `m` factors
into a product of one-dimensional Gaussian moments of total degree `lᵢ + mᵢ`.
Requires `α + β > 0` so that the Gaussian integrals converge. -/
theorem overlap_primitiveGTO_same_center (α β : ℝ) (R : ℝ³) (l m : Fin 3 → ℕ) (hαβ : α + β > 0) :
    overlap (primitiveGTO α R l) (primitiveGTO β R m) =
      ∏ i : Fin 3, gaussianMoment (l i + m i) (α + β) := by
  -- Rewrite the integrand as a product of 1D factors: combine polynomials and exponentials
  have hsimp : ∀ r : ℝ³,
      ((∏ i : Fin 3, (r i - R i) ^ l i) * Real.exp (-α * ∑ i : Fin 3, (r i - R i) ^ 2)) *
        ((∏ i : Fin 3, (r i - R i) ^ m i) * Real.exp (-β * ∑ i : Fin 3, (r i - R i) ^ 2)) =
        ∏ i : Fin 3, ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2)) := by
    calc
      ((∏ i, (r i - R i) ^ l i) * Real.exp (-α * ∑ i, (r i - R i) ^ 2)) *
        ((∏ i, (r i - R i) ^ m i) * Real.exp (-β * ∑ i, (r i - R i) ^ 2))
      = ((∏ i, (r i - R i) ^ l i) * (∏ i, (r i - R i) ^ m i)) *
          (Real.exp (-α * ∑ i, (r i - R i) ^ 2) * Real.exp (-β * ∑ i, (r i - R i) ^ 2)) := by ring
      _ = ((∏ i, (r i - R i) ^ l i) * (∏ i, (r i - R i) ^ m i)) *
          Real.exp ((-α * ∑ i, (r i - R i) ^ 2) + (-β * ∑ i, (r i - R i) ^ 2)) := by rw [Real.exp_add]
      _ = (∏ i, (r i - R i) ^ (l i + m i)) *
          Real.exp (-(α + β) * ∑ i, (r i - R i) ^ 2) := by
        simp [Finset.prod_mul_distrib, pow_add]; ring
      _ = ∏ i, ((r i - R i) ^ (l i + m i) * Real.exp (-(α + β) * (r i - R i) ^ 2)) := by
        rw [exp_neg_mul_sq_sum_eq_prod (α + β) (fun i => r i - R i), Finset.prod_mul_distrib]
  unfold overlap primitiveGTO
  conv_lhs =>
    arg 2; intro r; rw [hsimp r]
  -- Translate R → 0, then factor into product of 1D integrals
  rw [integral_translate (fun r => ∏ i : Fin 3,
    (r i ^ (l i + m i) * Real.exp (-(α + β) * (r i) ^ 2))) R]
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
theorem overlap_primitiveGTO_diff_center (α β : ℝ) (hαβ : α + β ≠ 0)
    (R₁ R₂ : ℝ³) (l m : Fin 3 → ℕ) :
    overlap (primitiveGTO α R₁ l) (primitiveGTO β R₂ m) =
      Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        ∏ i : Fin 3, ∫ x : ℝ,
          (x + (α * R₁ i + β * R₂ i) / (α + β) - R₁ i) ^ (l i) *
          (x + (α * R₁ i + β * R₂ i) / (α + β) - R₂ i) ^ (m i) *
          Real.exp (-(α + β) * x ^ 2) := by
  -- Gaussian product center P = (α·R₁ + β·R₂) / (α+β)
  set P : ℝ³ := fun i => (α * R₁ i + β * R₂ i) / (α + β) with hP
  -- Completing the square, lifted to ℝ³
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
      rw [show P i = (α * R₁ i + β * R₂ i) / (α + β) from rfl]
      exact complete_square α β (r i) (R₁ i) (R₂ i) hαβ
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
  -- Factor exp(-(α+β)·∑(r-P)²) = ∏ exp(-(α+β)·(rᵢ-Pᵢ)²)
  have hintegrand_eq :
      (fun r : ℝ³ => (∏ i : Fin 3, (r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * ∑ i : Fin 3, (r i - P i) ^ 2)) =
      (fun r : ℝ³ => ∏ i : Fin 3, (((r i - R₁ i) ^ l i * (r i - R₂ i) ^ m i) *
        Real.exp (-(α + β) * (r i - P i) ^ 2))) := by
    ext r
    rw [exp_neg_mul_sq_sum_eq_prod (α + β) (fun i => r i - P i)]
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
  sorry

/-- The zeroth Boys function `F₀(t) = ∫₀¹ exp(-t·u²) du`. This is the kernel that appears in
the closed form of the nuclear attraction and two-electron repulsion integrals for s-type
Gaussians. -/
noncomputable def boys0 (t : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-t * u ^ 2)

/-- Nuclear attraction integral of two s-type primitive GTOs against a nucleus at `C`:
  `V = (2π/(α+β)) · exp(-αβ/(α+β)·‖R₁-R₂‖²) · F₀((α+β)·‖P-C‖²)`,
where `P = (αR₁+βR₂)/(α+β)` is the Gaussian product center. -/
theorem nuclearAttraction_primitiveGTO_s
    (α β : ℝ) (hαβ : α + β ≠ 0) (R₁ R₂ C : ℝ³) :
    nuclearAttraction C (primitiveGTO_s α R₁) (primitiveGTO_s β R₂) =
      (2 * π / (α + β)) *
        Real.exp (-(α * β) / (α + β) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        boys0 ((α + β) *
          ∑ i : Fin 3,
            ((α * R₁ i + β * R₂ i) / (α + β) - C i) ^ 2) := by
  sorry

/-- Two-electron repulsion integral of four s-type primitive GTOs. With
  `P = (α₁R₁+α₂R₂)/(α₁+α₂)`, `Q = (α₃R₃+α₄R₄)/(α₃+α₄)`, `p = α₁+α₂`, `q = α₃+α₄`, the closed
form involves the zeroth Boys function evaluated at `pq/(p+q) · ‖P-Q‖²`. -/
theorem electronRepulsion_primitiveGTO_s
    (α₁ α₂ α₃ α₄ : ℝ) (_ : α₁ + α₂ ≠ 0) (_ : α₃ + α₄ ≠ 0)
    (_ : (α₁ + α₂) + (α₃ + α₄) ≠ 0)
    (R₁ R₂ R₃ R₄ : ℝ³) :
    electronRepulsion (primitiveGTO_s α₁ R₁) (primitiveGTO_s α₂ R₂)
        (primitiveGTO_s α₃ R₃) (primitiveGTO_s α₄ R₄) =
      (2 * π ^ (5/2 : ℝ)) /
        ((α₁ + α₂) * (α₃ + α₄) * Real.sqrt ((α₁ + α₂) + (α₃ + α₄))) *
        Real.exp (-(α₁ * α₂) / (α₁ + α₂) * ∑ i : Fin 3, (R₁ i - R₂ i) ^ 2) *
        Real.exp (-(α₃ * α₄) / (α₃ + α₄) * ∑ i : Fin 3, (R₃ i - R₄ i) ^ 2) *
        boys0 ((α₁ + α₂) * (α₃ + α₄) / ((α₁ + α₂) + (α₃ + α₄)) *
          ∑ i : Fin 3,
            ((α₁ * R₁ i + α₂ * R₂ i) / (α₁ + α₂) -
             (α₃ * R₃ i + α₄ * R₄ i) / (α₃ + α₄)) ^ 2) := by
  sorry

end GTO
