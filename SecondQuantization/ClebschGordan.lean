import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!

# Clebsch-Gordan Coefficients

This file formalizes the Clebsch-Gordan coefficients, which describe the coupling of two
angular momenta in quantum mechanics:

  |J M⟩ = Σ_{m₁,m₂} ⟨j₁ m₁, j₂ m₂ | J M⟩  |j₁ m₁⟩ ⊗ |j₂ m₂⟩

These coefficients encode how the tensor product of two irreducible SO(3) representations
decomposes into a direct sum of irreducibles:

  V_{j₁} ⊗ V_{j₂} ≅ ⊕_{J = |j₁ - j₂|}^{j₁ + j₂} V_J

## Angular momentum conventions

Angular momentum quantum numbers can be nonnegative integers or half-integers.
To avoid fractions, we use the "2×" convention:

* `j` is represented by `2j : ℕ` — so `j = 0, 1/2, 1, 3/2, ...` maps to `0, 1, 2, 3, ...`
* `m` is represented by `2m : ℤ` — so `m = ..., -j, -j+1, ..., j` maps to `..., -2j, -2j+2, ..., 2j`

The parity condition `j ± m ∈ ℕ` becomes `2j ≡ 2m (mod 2)`.

## Main definitions

* `validProj twoJ twoM` — predicate: `|2m| ≤ 2j` and `2m ≡ 2j (mod 2)`
* `triangleCond a b c` — the triangle inequality `|j₁ - j₂| ≤ J ≤ j₁ + j₂` with parity
* `projSet twoJ` — the finite set of valid projections for a given `j`
* `jPlusM`, `jMinusM` — convert `2j, 2m` to actual `j ± m` as `ℕ`
* `clebschGordan a b c α β γ` — the CG coefficient `⟨j₁ m₁, j₂ m₂ | J M⟩ : ℝ`
* `wigner3j a b c α β γ` — the Wigner 3j-symbol

## Main theorems

* Selection rules (vanishing conditions) — proven from the definition
* `coupleWithZero` — coupling with `j = 0` gives a Kronecker delta
* Condon-Shortley phase convention — the coefficient with maximal `m₁` is positive
* Orthogonality relations — stated
* Symmetry relations — stated

## References

* M. E. Rose, *Elementary Theory of Angular Momentum* (1957)
* A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (1957)
* D. M. Brink and G. R. Satchler, *Angular Momentum* (1968)

-/

namespace ClebschGordan

open Real
open Nat

/-! ### Validity predicates -/

/-- The triangle condition for three angular momenta `j₁, j₂, J` (given as `2j₁, 2j₂, 2J`):
`|j₁ - j₂| ≤ J ≤ j₁ + j₂` and `j₁ + j₂ + J` is an integer (parity condition). -/
def triangleCond (a b c : ℕ) : Prop :=
  |(a : ℤ) - (b : ℤ)| ≤ (c : ℤ) ∧ (c : ℤ) ≤ (a : ℤ) + (b : ℤ) ∧ (a + b + c) % 2 = 0

/-- A valid projection `m` for angular momentum `j` satisfies `|m| ≤ j` and `j ± m ∈ ℕ`.
In the 2× convention: `|2m| ≤ 2j` and `2m ≡ 2j (mod 2)`. -/
def validProj (twoJ : ℕ) (twoM : ℤ) : Prop :=
  |twoM| ≤ (twoJ : ℤ) ∧ ((twoJ : ℤ) - twoM) % 2 = 0

/-! ### Decidable instances

We need decidable instances for our predicates to use them in `if` expressions
and `Finset.filter`.
-/

/-- `triangleCond` is decidable because all its constituent relations are decidable. -/
instance triangleCond_decidable (a b c : ℕ) : Decidable (triangleCond a b c) := by
  unfold triangleCond; infer_instance

/-- `validProj` is decidable because `|·| ≤ ·` and `%` on `ℤ` are decidable. -/
instance validProj_decidable (twoJ : ℕ) (twoM : ℤ) : Decidable (validProj twoJ twoM) := by
  unfold validProj; infer_instance

/-- `validProj` as a decidable predicate for use in `Finset.filter`. -/
instance validProj_decidablePred (twoJ : ℕ) : DecidablePred (validProj twoJ) := by
  intro twoM; unfold validProj; infer_instance

/-- The finite set of all valid projection quantum numbers `2m` for a given `2j`. -/
def projSet (twoJ : ℕ) : Finset ℤ :=
  Finset.filter (validProj twoJ) (Finset.Icc (-(twoJ : ℤ)) (twoJ : ℤ))

lemma projSet_nonempty (twoJ : ℕ) : (projSet twoJ).Nonempty := by
  refine ⟨(twoJ : ℤ), ?_⟩
  have h_valid : validProj twoJ (twoJ : ℤ) := by
    unfold validProj
    constructor
    · simp
    · simp
  have h_mem_Icc : (twoJ : ℤ) ∈ Finset.Icc (-(twoJ : ℤ)) (twoJ : ℤ) := by
    simp
  simp [projSet, Finset.mem_filter, h_valid, h_mem_Icc]

lemma validProj_mem_projSet (twoJ : ℕ) (twoM : ℤ) (h : validProj twoJ twoM) :
    twoM ∈ projSet twoJ := by
  rcases h with ⟨hle, hpar⟩
  have h_mem_Icc : twoM ∈ Finset.Icc (-(twoJ : ℤ)) (twoJ : ℤ) := by
    have hrange : -(twoJ : ℤ) ≤ twoM ∧ twoM ≤ (twoJ : ℤ) :=
      abs_le.mp hle
    simp [hrange.1, hrange.2]
  have h_valid : validProj twoJ twoM := ⟨hle, hpar⟩
  simp [projSet, Finset.mem_filter, h_mem_Icc, h_valid]

lemma card_projSet (twoJ : ℕ) : (projSet twoJ).card = twoJ + 1 := by
  sorry  -- Standard fact: there are 2j+1 valid m values

/-! ### Helper functions for converting 2× convention to actual quantum numbers

All expressions like `j + m` become `(2j + 2m)/2`. Given `validProj twoJ twoM`, we know
`-twoJ ≤ twoM ≤ twoJ` and `twoJ ≡ twoM (mod 2)`, so `(twoJ ± twoM)/2` is a nonnegative integer.
-/

/-- `(j + m)` as a natural number, given `2j` and `2m`. Requires `validProj twoJ twoM`
for correctness (the caller must ensure this, otherwise the result is 0). -/
def jPlusM (twoJ : ℕ) (twoM : ℤ) : ℕ :=
  (((twoJ : ℤ) + twoM) / 2).toNat

/-- `(j - m)` as a natural number, given `2j` and `2m`. Requires `validProj twoJ twoM`
for correctness. -/
def jMinusM (twoJ : ℕ) (twoM : ℤ) : ℕ :=
  (((twoJ : ℤ) - twoM) / 2).toNat

/-- `(j₁ + j₂ - J)` as a natural number, given `2j₁, 2j₂, 2J`.
Requires `triangleCond` for correctness. -/
def j1j2_minus_J (a b c : ℕ) : ℕ :=
  (((a : ℤ) + (b : ℤ) - (c : ℤ)) / 2).toNat

/-- `(j₁ - j₂ + J)` as a natural number. -/
def j1_j2_plus_J (a b c : ℕ) : ℕ :=
  (((a : ℤ) - (b : ℤ) + (c : ℤ)) / 2).toNat

/-- `(-j₁ + j₂ + J)` as a natural number. -/
def nj1_j2_plus_J (a b c : ℕ) : ℕ :=
  (((-(a : ℤ)) + (b : ℤ) + (c : ℤ)) / 2).toNat

/-- `(j₁ + j₂ + J + 1)` as a natural number — the denominator factorial argument in Δ. -/
def j1j2J_plus_one (a b c : ℕ) : ℕ :=
  ((a + b + c) / 2 + 1 : ℕ)

lemma jPlusM_nonneg (twoJ : ℕ) (twoM : ℤ) (h : validProj twoJ twoM) : 0 ≤ (twoJ : ℤ) + twoM := by
  rcases h with ⟨hle, _⟩
  have hlower : -(twoJ : ℤ) ≤ twoM := by
    have := abs_le.mp hle
    exact this.1
  linarith

lemma jMinusM_nonneg (twoJ : ℕ) (twoM : ℤ) (h : validProj twoJ twoM) : 0 ≤ (twoJ : ℤ) - twoM := by
  rcases h with ⟨hle, _⟩
  have hupper : twoM ≤ (twoJ : ℤ) := by
    have := abs_le.mp hle
    exact this.2
  linarith

lemma jPlusM_add_jMinusM (twoJ : ℕ) (twoM : ℤ) (h : validProj twoJ twoM) :
    (jPlusM twoJ twoM : ℤ) + (jMinusM twoJ twoM : ℤ) = (twoJ : ℤ) := by
  -- This identity follows from the definitions and the parity condition.
  -- The proof requires showing that integer division by 2 is exact when the
  -- numerator is even and nonnegative. We defer the full proof.
  sorry

/-! ### The triangle coefficient Δ

Δ(j₁, j₂, J) = √[ (j₁+j₂-J)! · (j₁-j₂+J)! · (-j₁+j₂+J)! / (j₁+j₂+J+1)! ]

This factor depends only on the angular momenta, not on the projections.
-/

/-- The triangle (Δ) coefficient, which depends only on the three angular momenta
and is independent of the projections. -/
noncomputable def triangleCoeff (a b c : ℕ) : ℝ :=
  Real.sqrt (
    ((Nat.factorial (j1j2_minus_J a b c) : ℝ) *
     (Nat.factorial (j1_j2_plus_J a b c) : ℝ) *
     (Nat.factorial (nj1_j2_plus_J a b c) : ℝ)) /
    (Nat.factorial (j1j2J_plus_one a b c) : ℝ)
  )

lemma triangleCoeff_nonneg (a b c : ℕ) : 0 ≤ triangleCoeff a b c :=
  Real.sqrt_nonneg _

/-! ### The projection-dependent prefactor

P(j₁,j₂,J; m₁,m₂,M) = √[ (2J+1) · Π (j₁±m₁)! · (j₂±m₂)! · (J±M)! ]

This factor is symmetric in the ± sign for each angular momentum.
-/

/-- The projection-dependent prefactor in the Racah formula, which is
`√[(2J+1) · (j₁+m₁)! · (j₁-m₁)! · (j₂+m₂)! · (j₂-m₂)! · (J+M)! · (J-M)!]`. -/
noncomputable def projectionPrefactor (a b c : ℕ) (α β γ : ℤ) : ℝ :=
  Real.sqrt (
    ((c : ℝ) + 1) *
    ((Nat.factorial (jPlusM a α) : ℝ) *
     (Nat.factorial (jMinusM a α) : ℝ) *
     (Nat.factorial (jPlusM b β) : ℝ) *
     (Nat.factorial (jMinusM b β) : ℝ) *
     (Nat.factorial (jPlusM c γ) : ℝ) *
     (Nat.factorial (jMinusM c γ) : ℝ))
  )

lemma projectionPrefactor_nonneg (a b c : ℕ) (α β γ : ℤ) : 0 ≤ projectionPrefactor a b c α β γ :=
  Real.sqrt_nonneg _

/-! ### The Racah sum

The alternating sum in Racah's formula:
  Σ_{k = 0}^{kmax} (-1)^k / [k! · (j₁+j₂-J-k)! · (j₁-m₁-k)! · (j₂+m₂-k)! · (J-j₁+j₂-k)! · (J-M-k)!]

where `kmax = min(j₁+j₂-J, j₁-m₁, j₂+m₂, J-j₁+j₂, J-M)`.
-/

/-- The upper bound for `k` in the Racah sum: `min` of all the expressions that must remain
nonnegative when `k` is subtracted. -/
def racahSumMax (a b c : ℕ) (α β γ : ℤ) : ℕ :=
  min (min (j1j2_minus_J a b c) (jMinusM a α))
      (min (min (jPlusM b β) (j1_j2_plus_J a b c)) (jMinusM c γ))

/-- The set of `k` values over which the Racah sum runs: `k : ℕ` with `k ≤ kmax`. -/
def racahSumRange (a b c : ℕ) (α β γ : ℤ) : Finset ℕ :=
  Finset.range (racahSumMax a b c α β γ + 1)

/-- A single term in the Racah sum. -/
noncomputable def racahTerm (a b c : ℕ) (α β γ : ℤ) (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) /
  (((Nat.factorial k : ℝ) *
    (Nat.factorial (j1j2_minus_J a b c - k) : ℝ) *
    (Nat.factorial (jMinusM a α - k) : ℝ) *
    (Nat.factorial (jPlusM b β - k) : ℝ) *
    (Nat.factorial (j1_j2_plus_J a b c - k) : ℝ) *
    (Nat.factorial (jMinusM c γ - k) : ℝ)))

/-- The alternating Racah sum:
  Σ_{k = 0}^{kmax} (-1)^k / [k! · Π (bound - k)!] -/
noncomputable def racahSum (a b c : ℕ) (α β γ : ℤ) : ℝ :=
  Finset.sum (racahSumRange a b c α β γ) (fun k => racahTerm a b c α β γ k)

/-! ### The Clebsch-Gordan coefficient

The full Racah formula for the Clebsch-Gordan coefficient:

⟨j₁ m₁, j₂ m₂ | J M⟩ = δ(m₁ + m₂, M) · Δ(j₁, j₂, J) ·
  √[(2J+1) · Π (jᵢ ± mᵢ)! · (J ± M)!] ·
  Σ_k (-1)^k / [k! · (j₁+j₂-J-k)! · (j₁-m₁-k)! · (j₂+m₂-k)! · (J-j₁+j₂-k)! · (J-M-k)!]

If any of the selection rules is violated, the coefficient is zero.
-/

/-- The Clebsch-Gordan coefficient `⟨j₁ m₁, j₂ m₂ | J M⟩` computed via Racah's explicit formula.

All arguments use the 2× convention:
* `a = 2j₁`, `b = 2j₂`, `c = 2J` are `ℕ`
* `α = 2m₁`, `β = 2m₂`, `γ = 2M` are `ℤ`

Returns `0` if any selection rule is violated. -/
noncomputable def clebschGordan (a b c : ℕ) (α β γ : ℤ) : ℝ :=
  if α + β ≠ γ then 0
  else if ¬ triangleCond a b c then 0
  else if ¬ (validProj a α ∧ validProj b β ∧ validProj c γ) then 0
  else triangleCoeff a b c * projectionPrefactor a b c α β γ * racahSum a b c α β γ

/-- Notation for the Clebsch-Gordan coefficient:
`⟨2j₁ 2m₁, 2j₂ 2m₂ | 2J 2M⟩` -/
notation "⟨" a:max "," α:max ";" b:max "," β:max "|" c:max "," γ:max "⟩" => clebschGordan a b c α β γ

/-! ### Selection rules -/

/-- **Selection rule (m-sum):** The CG coefficient vanishes unless `m₁ + m₂ = M`. -/
theorem clebschGordan_eq_zero_of_m_sum_ne (a b c : ℕ) (α β γ : ℤ) (h : α + β ≠ γ) :
    clebschGordan a b c α β γ = 0 := by
  simp [clebschGordan, h]

/-- **Selection rule (triangle):** The CG coefficient vanishes unless `|j₁ - j₂| ≤ J ≤ j₁ + j₂`
and `j₁ + j₂ + J` is an integer. -/
theorem clebschGordan_eq_zero_of_not_triangle (a b c : ℕ) (α β γ : ℤ) (h : ¬ triangleCond a b c) :
    clebschGordan a b c α β γ = 0 := by
  simp [clebschGordan, h]

/-- **Selection rule (projection):** The CG coefficient vanishes unless all projections
are valid for their respective angular momenta. -/
theorem clebschGordan_eq_zero_of_invalid_proj (a b c : ℕ) (α β γ : ℤ)
    (h : ¬ (validProj a α ∧ validProj b β ∧ validProj c γ)) :
    clebschGordan a b c α β γ = 0 := by
  simp [clebschGordan, h]

/-- **Combined selection rule:** For a nonzero CG coefficient, all three conditions are
necessary (though not sufficient — the coefficient can still vanish accidentally). -/
theorem clebschGordan_ne_zero_imp (a b c : ℕ) (α β γ : ℤ) (hcg : clebschGordan a b c α β γ ≠ 0) :
    α + β = γ ∧ triangleCond a b c ∧ validProj a α ∧ validProj b β ∧ validProj c γ := by
  have h_sum : α + β = γ := by
    by_contra! h
    apply hcg
    simp [clebschGordan, h]
  have h_tri : triangleCond a b c := by
    by_contra! h
    apply hcg
    simp [clebschGordan, h]
  have h_proj : validProj a α ∧ validProj b β ∧ validProj c γ := by
    by_cases hpa : validProj a α
    · by_cases hpb : validProj b β
      · by_cases hpc : validProj c γ
        · exact ⟨hpa, hpb, hpc⟩
        · exact absurd (by simp [clebschGordan, hpa, hpb, hpc]) hcg
      · exact absurd (by simp [clebschGordan, hpa, hpb]) hcg
    · exact absurd (by simp [clebschGordan, hpa]) hcg
  exact ⟨h_sum, h_tri, h_proj.1, h_proj.2.1, h_proj.2.2⟩

/-! ### Coupling with zero angular momentum

When one of the angular momenta is zero, the CG coefficient reduces to a Kronecker delta.
Physically: coupling any state with the vacuum (j=0) leaves it unchanged.
-/

/-- The CG coefficient for coupling with `j₂ = 0`: `⟨j m, 0 0 | J M⟩ = δ_{j,J} · δ_{m,M}`,
provided `m` is a valid projection for `j`.

When `m` is valid for `j`, the CG coefficient is 1 if `j = J` and `m = M`, and 0 otherwise.
If `m` is not a valid projection for `j`, the CG coefficient is always 0 (by the selection rules).

The algebraic proof that the Racah formula simplifies to 1 when all selection rules are
satisfied and `j = J`, `m = M` with `j₂ = 0` is deferred. -/
theorem coupleWithZero (a c : ℕ) (α γ : ℤ) (hpa : validProj a α) :
    clebschGordan a 0 c α 0 γ = if a = c ∧ α = γ then 1 else 0 := by
  unfold clebschGordan
  simp only [add_zero]
  by_cases hαγ : α = γ
  · rw [hαγ]
    simp
    by_cases h_eq : a = c
    · rw [h_eq]
      simp
      have hproj0 : validProj 0 (0 : ℤ) := by unfold validProj; simp
      have hpa' : validProj c α := h_eq ▸ hpa
      have h_and : validProj c α ∧ validProj 0 0 ∧ validProj c α := ⟨hpa', hproj0, hpa'⟩
      simp [h_and]
      -- Remaining: triangleCoeff c 0 c * projectionPrefactor c 0 c α 0 α *
      --   racahSum c 0 c α 0 α = 1
      sorry
    · by_cases htri : triangleCond a 0 c
      · rcases htri with ⟨hle1, hle2, hpar⟩
        -- triangleCond a 0 c implies a = c, contradiction
        have h_ac : (a : ℤ) = (c : ℤ) := by
          have h1 : |(a : ℤ) - (0 : ℤ)| ≤ (c : ℤ) := hle1
          have h2 : (c : ℤ) ≤ (a : ℤ) + (0 : ℤ) := hle2
          simp at h1 h2; omega
        omega
      · simp [htri, h_eq]
  · simp [hαγ]

/-! ### Phase conventions

The Condon-Shortley phase convention sets the CG coefficient with maximal `m₁`
(and `m₂ = M - j₁`, `M = J`) to be positive:
  `⟨j₁, j₁; j₂, J - j₁ | J, J⟩ > 0`
-/

/-- **Condon-Shortley phase convention:** The CG coefficient with the maximal `m₁` value
is strictly positive. Here `a = 2j₁`, `b = 2j₂`, `c = 2J`, and the projections are
`α = a = 2j₁`, `β = c - a = 2J - 2j₁`, `γ = c = 2J`. -/
theorem condonShortley_phase (a b c : ℕ) (h_triangle : triangleCond a b c) :
    0 < clebschGordan a b c a ((c : ℤ) - (a : ℤ)) c := by
  -- The proof shows that with maximal m₁ and m₂ = J-j₁, the Racah sum has a single
  -- positive term and all factors are positive.
  sorry

/-! ### Orthogonality relations

The CG coefficients are matrix elements of a unitary transformation. Hence they satisfy
two orthogonality relations (the rows and columns of the transformation matrix are orthonormal).
-/

/-- **First orthogonality relation** (orthogonality of rows):
  Σ_{m₁,m₂} ⟨j₁ m₁, j₂ m₂ | J M⟩ ⟨j₁ m₁, j₂ m₂ | J' M'⟩ = δ_{J,J'} · δ_{M,M'}

This states that the coupled basis vectors |J M⟩ are orthonormal when expressed in the
uncoupled basis. -/
theorem orthogonality_rows (a b c c' : ℕ) (γ γ' : ℤ) (h_triangle : triangleCond a b c)
    (h_triangle' : triangleCond a b c') :
    (Finset.sum (projSet a) fun α =>
      Finset.sum (projSet b) fun β =>
        clebschGordan a b c α β γ * clebschGordan a b c' α β γ') =
    if c = c' ∧ γ = γ' then 1 else 0 := by
  sorry

/-- **Second orthogonality relation** (orthogonality of columns):
  Σ_{J,M} ⟨j₁ m₁, j₂ m₂ | J M⟩ ⟨j₁ m₁', j₂ m₂' | J M⟩ = δ_{m₁,m₁'} · δ_{m₂,m₂'}

This states that the uncoupled basis vectors |j₁ m₁⟩ ⊗ |j₂ m₂⟩ are orthonormal when
expressed in the coupled basis. -/
theorem orthogonality_columns (a b : ℕ) (α α' β β' : ℤ)
    (hpa : validProj a α) (hpa' : validProj a α') (hpb : validProj b β) (hpb' : validProj b β') :
    (Finset.sum (Finset.range (a + b + 1)) fun c =>
      Finset.sum (projSet c) fun γ =>
        clebschGordan a b c α β γ * clebschGordan a b c α' β' γ) =
    if α = α' ∧ β = β' then 1 else 0 := by
  sorry

/-! ### Symmetry relations

The CG coefficients satisfy several symmetry relations relating different orderings of
the three angular momenta. These are most cleanly expressed using the Wigner 3j-symbols.
-/

/-- **Swap symmetry:** Swapping the two source angular momenta introduces a phase factor:
  `⟨j₁ m₁, j₂ m₂ | J M⟩ = (-1)^{j₁ + j₂ - J} ⟨j₂ m₂, j₁ m₁ | J M⟩`
-/
theorem symmetry_swap (a b c : ℕ) (α β γ : ℤ)
    (h_triangle : triangleCond a b c) :
    clebschGordan a b c α β γ =
      ((-1 : ℝ) ^ (((a : ℤ) + (b : ℤ) - (c : ℤ)) / 2).toNat) * clebschGordan b a c β α γ := by
  sorry

/-- **Space inversion (parity) symmetry:**
  `⟨j₁ m₁, j₂ m₂ | J M⟩ = (-1)^{j₁ + j₂ - J} ⟨j₁ -m₁, j₂ -m₂ | J -M⟩`
-/
theorem symmetry_parity (a b c : ℕ) (α β γ : ℤ)
    (h_triangle : triangleCond a b c) :
    clebschGordan a b c α β γ =
      ((-1 : ℝ) ^ (((a : ℤ) + (b : ℤ) - (c : ℤ)) / 2).toNat) *
      clebschGordan a b c (-α) (-β) (-γ) := by
  sorry

/-! ### Wigner 3j-symbols

The Wigner 3j-symbol `(j₁ j₂ J; m₁ m₂ M)` is a more symmetric version of the CG coefficient:

  (j₁  j₂  J )
  (m₁  m₂  M ) = (-1)^{j₁ - j₂ - M} / √(2J + 1) · ⟨j₁ m₁, j₂ m₂ | J, -M⟩

The 3j-symbol has higher symmetry: it is invariant under even permutations of the columns
and gains a phase (-1)^{j₁+j₂+J} under odd permutations.
-/

/-- The Wigner 3j-symbol, related to the CG coefficient by a phase and normalization.

All arguments use the 2× convention:
* `a = 2j₁`, `b = 2j₂`, `c = 2J` are `ℕ`
* `α = 2m₁`, `β = 2m₂`, `γ = 2M` are `ℤ`

The 3j-symbol vanishes unless `m₁ + m₂ + M = 0`. -/
noncomputable def wigner3j (a b c : ℕ) (α β γ : ℤ) : ℝ :=
  if ¬ (α + β + γ = 0) then 0
  else if ¬ triangleCond a b c then 0
  else if ¬ (validProj a α ∧ validProj b β ∧ validProj c γ) then 0
  else
    ((-1 : ℝ) ^ ((((a : ℤ) - (b : ℤ) - γ) / 2).toNat)) /
    Real.sqrt ((c : ℝ) + 1) *
    clebschGordan a b c α β (-γ)

/-- The CG coefficient in terms of the Wigner 3j-symbol:
  `⟨j₁ m₁, j₂ m₂ | J M⟩ = (-1)^{j₁ - j₂ + M} · √(2J + 1) · (j₁ j₂ J; m₁ m₂ -M)`
-/
theorem clebschGordan_of_wigner3j (a b c : ℕ) (α β γ : ℤ) :
    clebschGordan a b c α β γ =
      ((-1 : ℝ) ^ ((((a : ℤ) - (b : ℤ) + γ) / 2).toNat)) *
      Real.sqrt ((c : ℝ) + 1) *
      wigner3j a b c α β (-γ) := by
  unfold wigner3j
  by_cases hsum : α + β + (-γ) = 0
  · -- α + β = γ, so CG may be nonzero
    have hγ : α + β = γ := by linarith
    -- Expands to the CG definition; needs algebraic verification
    sorry
  · -- α + β ≠ γ, so CG = 0 and wigner3j = 0
    have hcg : clebschGordan a b c α β γ = 0 :=
      clebschGordan_eq_zero_of_m_sum_ne a b c α β γ (by
        intro h; apply hsum; linarith)
    simp [hsum, hcg]

/-! ### Wigner 3j-symbol symmetries

The 3j-symbol is highly symmetric:
1. **Even permutation:** invariant under cyclic permutation of columns
2. **Odd permutation:** gains factor `(-1)^{j₁ + j₂ + J}`
3. **Space inversion:** `(j₁ j₂ J; -m₁ -m₂ -M) = (-1)^{j₁+j₂+J} (j₁ j₂ J; m₁ m₂ M)`
-/

/-- The 3j-symbol is invariant under even (cyclic) permutations of its columns. -/
theorem wigner3j_cyclic (a b c : ℕ) (α β γ : ℤ) :
    wigner3j a b c α β γ = wigner3j b c a β γ α := by
  sorry

/-- The 3j-symbol is invariant under even (cyclic) permutations of its columns. -/
theorem wigner3j_cyclic' (a b c : ℕ) (α β γ : ℤ) :
    wigner3j a b c α β γ = wigner3j c a b γ α β := by
  sorry

/-- Under an odd permutation (swap of two columns), the 3j-symbol gains a factor
`(-1)^{j₁ + j₂ + J}`. -/
theorem wigner3j_swap (a b c : ℕ) (α β γ : ℤ) :
    wigner3j b a c β α γ =
      ((-1 : ℝ) ^ ((((a : ℤ) + (b : ℤ) + (c : ℤ)) / 2).toNat)) *
      wigner3j a b c α β γ := by
  sorry

/-- Space inversion: flipping all projection signs introduces a factor `(-1)^{j₁+j₂+J}`. -/
theorem wigner3j_parity (a b c : ℕ) (α β γ : ℤ) :
    wigner3j a b c (-α) (-β) (-γ) =
      ((-1 : ℝ) ^ ((((a : ℤ) + (b : ℤ) + (c : ℤ)) / 2).toNat)) *
      wigner3j a b c α β γ := by
  sorry

end ClebschGordan
