import SecondQuantization.Basic
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

namespace Fock

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
  `T = -½ ∫ φ(r) · (Δ ψ)(r) dr` where `Δ` is the Laplacian on `ℝ³`. -/
noncomputable def kinetic (φ ψ : ℝ³ → ℝ) : ℝ :=
  -(1/2) * ∫ r : ℝ³, φ r *
    (∑ i : Fin 3, iteratedFDeriv ℝ 2 ψ r (fun _ ↦ Pi.single i 1))

/-- The one-electron core Hamiltonian matrix element for nuclei `{(Z_k, C_k) : k}`:
  `h = T + ∑ₖ -Zₖ · ⟨φ | 1/‖r - Cₖ‖ | ψ⟩`. -/
noncomputable def coreHamiltonian {ι : Type} [Fintype ι]
    (Z : ι → ℝ) (C : ι → ℝ³) (φ ψ : ℝ³ → ℝ) : ℝ :=
  kinetic φ ψ + ∑ k : ι, (- Z k) * nuclearAttraction (C k) φ ψ

/-! ## Explicit integral evaluations -/

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

end Fock
