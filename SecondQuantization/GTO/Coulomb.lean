import SecondQuantization.GTO.Defs

namespace GTO

open Real MeasureTheory

/-- The zeroth Boys function `F₀(t) = ∫₀¹ exp(-t·u²) du`. This is the kernel that appears in
the closed form of the nuclear attraction and two-electron repulsion integrals for s-type
Gaussians. -/
noncomputable def boys0 (t : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-t * u ^ 2)

/-- Nuclear attraction integral of two s-type primitive GTOs against a nucleus at `C`:
  `V = (2π/(α+β)) · exp(-αβ/(α+β)·‖R₁-R₂‖²) · F₀((α+β)·‖P-C‖²)`,
where `P = (αR₁+βR₂)/(α+β)` is the Gaussian product center. -/
theorem nuclearAttraction_primitiveGTO_s
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (R₁ R₂ C : ℝ³) :
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
    (α₁ α₂ α₃ α₄ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα₃ : 0 < α₃) (hα₄ : 0 < α₄)
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
