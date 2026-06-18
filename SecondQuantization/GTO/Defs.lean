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

noncomputable def coulomb (x y : ℝ³) : ℝ := 1 / √(∑ i, (x i - y i) ^ 2)

/-- The nuclear attraction integral for a nucleus at `C`:
  `V = ∫ φ(r) · (1 / ‖r - C‖) · ψ(r) dr` over `ℝ³`. -/
noncomputable def nuclearAttraction (C : ℝ³) (φ ψ : ℝ³ → ℝ) : ℝ :=
  ∫ r : ℝ³, φ r * coulomb r C * ψ r

/-- The two-electron repulsion integral (electron-electron interaction):
  `(φ₁ φ₂ | φ₃ φ₄) = ∫∫ φ₁(r₁) · φ₂(r₁) · (1 / ‖r₁ - r₂‖) · φ₃(r₂) · φ₄(r₂) dr₁ dr₂`. -/
noncomputable def electronRepulsion (φ₁ φ₂ φ₃ φ₄ : ℝ³ → ℝ) : ℝ :=
  ∫ r₁ : ℝ³, ∫ r₂ : ℝ³,
    φ₁ r₁ * φ₂ r₁ * coulomb r₁ r₂ * φ₃ r₂ * φ₄ r₂

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

end GTO
