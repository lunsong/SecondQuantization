import SecondQuantization.Basic
import Mathlib.Tactic

/-!

# SO(3) Lie Algebra and Action on ℝ³

This file defines the Lie algebra `so(3)` — the algebra of infinitesimal rotations
in three dimensions — and its action on `ℝ³` and on functions.

We use the well-known isomorphism `so(3) ≅ ℝ³` where the Lie bracket on `ℝ³`
is the cross product. This is the most natural representation for quantum chemistry
applications where `ℝ³` is the physical space.

## Main definitions

* `crossProd` — cross product on `ℝ³`
* `so3_lie_bracket` — the Lie bracket `[v, w] = v × w` on `ℝ³`
* `hatMap` — the linear map `ℝ³ → End(ℝ³)` sending `v` to `w ↦ v × w`
* `angularMomentumX`, `angularMomentumY`, `angularMomentumZ` — basis elements
* `so3_action_R3` — the defining representation on ℝ³

## Main theorems

* `lie_bracket_eq_cross` — the Lie bracket `[v, w]` equals `v × w`
* `hatMap_lie` — `[hat(v), hat(w)] = hat(v × w)` as endomorphisms
* `angularMomentum_commutation` — `[J_i, J_j] = ε_{ijk} J_k`

-/

namespace SO3

/-! ### Cross product on ℝ³ -/

/-- The cross product on ℝ³:
  `(v₀, v₁, v₂) × (w₀, w₁, w₂) = (v₁w₂ - v₂w₁, v₂w₀ - v₀w₂, v₀w₁ - v₁w₀)`. -/
def crossProd (v w : ℝ³) : ℝ³ :=
  ![v 1 * w 2 - v 2 * w 1,
    v 2 * w 0 - v 0 * w 2,
    v 0 * w 1 - v 1 * w 0]

@[simp] lemma crossProd_apply (v w : ℝ³) (i : Fin 3) : crossProd v w i =
    match i with
    | 0 => v 1 * w 2 - v 2 * w 1
    | 1 => v 2 * w 0 - v 0 * w 2
    | 2 => v 0 * w 1 - v 1 * w 0 := by
  fin_cases i <;> rfl

/-- The cross product is bilinear. -/
lemma crossProd_bilinear (v₁ v₂ w : ℝ³) (c : ℝ) :
    crossProd (c • v₁ + v₂) w = c • crossProd v₁ w + crossProd v₂ w := by
  ext i; fin_cases i <;> simp [crossProd, Pi.add_apply, Pi.smul_apply] <;> ring

lemma crossProd_bilinear_right (v w₁ w₂ : ℝ³) (c : ℝ) :
    crossProd v (c • w₁ + w₂) = c • crossProd v w₁ + crossProd v w₂ := by
  ext i; fin_cases i <;> simp [crossProd, Pi.add_apply, Pi.smul_apply] <;> ring

/-- The cross product is antisymmetric: `v × w = -(w × v)`. -/
@[simp] lemma crossProd_antisymm (v w : ℝ³) : crossProd v w = -crossProd w v := by
  ext i; fin_cases i <;> simp [crossProd] <;> ring

/-- The cross product satisfies the Jacobi identity:
  `u × (v × w) + v × (w × u) + w × (u × v) = 0`. -/
lemma crossProd_jacobi (u v w : ℝ³) :
    crossProd u (crossProd v w) + crossProd v (crossProd w u) + crossProd w (crossProd u v) = 0 := by
  ext i; fin_cases i <;> simp [crossProd, Pi.add_apply] <;> ring

/-- The scalar triple product: `u · (v × w)`. -/
def scalarTriple (u v w : ℝ³) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) +
  u 1 * (v 2 * w 0 - v 0 * w 2) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

/-- The scalar triple product is cyclic: `u · (v × w) = v · (w × u) = w · (u × v)`. -/
lemma scalarTriple_cyclic (u v w : ℝ³) :
    scalarTriple u v w = scalarTriple v w u ∧ scalarTriple v w u = scalarTriple w u v := by
  unfold scalarTriple
  constructor <;> ring

/-! ### The Lie algebra structure on ℝ³

ℝ³ with the cross product forms a Lie algebra isomorphic to so(3). The Lie bracket
is `[v, w] = v × w`. This satisfies antisymmetry and the Jacobi identity.
-/

/-- The Lie bracket on ℝ³ (cross product), making it into a Lie algebra isomorphic to so(3). -/
def lieBracket (v w : ℝ³) : ℝ³ := crossProd v w

/-- The Lie bracket is antisymmetric: `[v, w] = -[w, v]`. -/
@[simp] lemma lieBracket_antisymm (v w : ℝ³) : lieBracket v w = -lieBracket w v :=
  crossProd_antisymm v w

/-- The Lie bracket satisfies the Jacobi identity:
  `[u, [v, w]] + [v, [w, u]] + [w, [u, v]] = 0`. -/
lemma lieBracket_jacobi (u v w : ℝ³) :
    lieBracket u (lieBracket v w) + lieBracket v (lieBracket w u) + lieBracket w (lieBracket u v) = 0 :=
  crossProd_jacobi u v w

/-! ### Angular momentum basis -/

/-- The standard basis vectors of so(3) corresponding to infinitesimal rotations:
`e_x`, `e_y`, `e_z` (or equivalently `L_x`, `L_y`, `L_z`). -/
def angularMomentumX : ℝ³ := ![1, 0, 0]
def angularMomentumY : ℝ³ := ![0, 1, 0]
def angularMomentumZ : ℝ³ := ![0, 0, 1]

/-- Commutation relation: `[L_x, L_y] = L_z`. -/
lemma comm_Lx_Ly : lieBracket angularMomentumX angularMomentumY = angularMomentumZ := by
  ext i; fin_cases i <;> simp [lieBracket, crossProd, angularMomentumX, angularMomentumY, angularMomentumZ]

/-- Commutation relation: `[L_y, L_z] = L_x`. -/
lemma comm_Ly_Lz : lieBracket angularMomentumY angularMomentumZ = angularMomentumX := by
  ext i; fin_cases i <;> simp [lieBracket, crossProd, angularMomentumX, angularMomentumY, angularMomentumZ]

/-- Commutation relation: `[L_z, L_x] = L_y`. -/
lemma comm_Lz_Lx : lieBracket angularMomentumZ angularMomentumX = angularMomentumY := by
  ext i; fin_cases i <;> simp [lieBracket, crossProd, angularMomentumX, angularMomentumY, angularMomentumZ]

/-- The commutation relations of angular momentum in index form:
`[L_i, L_j] = ε_{ijk} L_k` where `ε` is the Levi-Civita symbol. -/
lemma angularMomentum_commutation (i j k : Fin 3) (h : (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1)) :
    lieBracket (match i with | 0 => angularMomentumX | 1 => angularMomentumY | 2 => angularMomentumZ)
               (match j with | 0 => angularMomentumX | 1 => angularMomentumY | 2 => angularMomentumZ) =
    (match k with | 0 => angularMomentumX | 1 => angularMomentumY | 2 => angularMomentumZ) := by
  rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  · exact comm_Lx_Ly
  · exact comm_Ly_Lz
  · exact comm_Lz_Lx

/-! ### The hat map: ℝ³ → End(ℝ³)

The "hat map" sends a vector `v ∈ ℝ³` to the linear endomorphism
`hat(v) : ℝ³ → ℝ³`, `w ↦ v × w`. This is the defining representation of so(3).
-/

/-- The hat map: a linear map from ℝ³ to linear endomorphisms of ℝ³.
`hat(v) w = v × w`. -/
def hatMap : ℝ³ →ₗ[ℝ] (ℝ³ →ₗ[ℝ] ℝ³) where
  toFun v := {
    toFun w := crossProd v w
    map_add' := fun w₁ w₂ => by
      ext i; fin_cases i <;> simp [crossProd, Pi.add_apply] <;> ring
    map_smul' := fun c w => by
      ext i; fin_cases i <;> simp [crossProd, Pi.smul_apply] <;> ring
  }
  map_add' v₁ v₂ := by
    ext w i; fin_cases i <;> simp [crossProd, Pi.add_apply] <;> ring
  map_smul' c v := by
    ext w i; fin_cases i <;> simp [crossProd, Pi.smul_apply] <;> ring

/-- `hat(v) w = v × w`. -/
@[simp] lemma hatMap_apply (v w : ℝ³) : hatMap v w = crossProd v w := rfl

/-- The hat map is injective. Proof: evaluate on basis vectors and compare components. -/
lemma hatMap_injective : Function.Injective hatMap := by
  intro v w h
  -- Apply the equality to each basis vector and expand fully using fin_cases
  have h_on_x := LinearMap.congr_fun h angularMomentumX
  have h_on_y := LinearMap.congr_fun h angularMomentumY
  have h_on_z := LinearMap.congr_fun h angularMomentumZ
  dsimp [hatMap, angularMomentumX, angularMomentumY, angularMomentumZ, crossProd] at h_on_x h_on_y h_on_z
  -- After dsimp, h_on_x, h_on_y, h_on_z are explicit vector equalities
  -- Extract component equalities by evaluating vector equalities at indices
  have hv0 : v 0 = w 0 := by
    have := congrArg (fun (u : ℝ³) => u 2) h_on_y
    -- this : ![-v 2, 0, v 0] 2 = ![-w 2, 0, w 0] 2
    -- which simplifies to v 0 = w 0
    simpa using this
  have hv1 : v 1 = w 1 := by
    have := congrArg (fun (u : ℝ³) => u 0) h_on_z
    -- this : ![v 1, -v 0, 0] 0 = ![w 1, -w 0, 0] 0
    simpa using this
  have hv2 : v 2 = w 2 := by
    have := congrArg (fun (u : ℝ³) => u 1) h_on_x
    -- this : ![0, v 2, -v 1] 1 = ![0, w 2, -w 1] 1
    simpa using this
  ext i; fin_cases i <;> assumption

/-- **Key identity:** The commutator of two hat-map endomorphisms equals the hat map of
their cross product: `[hat(v), hat(w)] = hat(v × w)` as endomorphisms of ℝ³.
Here `[A, B] = A ∘ B - B ∘ A` is the commutator of linear endomorphisms. -/
theorem hatMap_commutator (v w : ℝ³) :
    hatMap v ∘ₗ hatMap w - hatMap w ∘ₗ hatMap v = hatMap (crossProd v w) := by
  ext u i
  fin_cases i <;>
    simp [hatMap, crossProd, LinearMap.sub_apply, LinearMap.comp_apply, Pi.add_apply] <;>
    ring

/-- The Lie algebra structure on `End(ℝ³)` has bracket `[A, B] = A ∘ B - B ∘ A`.
The hat map is a Lie algebra homomorphism from `(ℝ³, ×)` to `(End(ℝ³), [·,·])`. -/
theorem hatMap_lie_hom (v w : ℝ³) :
    hatMap (lieBracket v w) = hatMap v * hatMap w - hatMap w * hatMap v := by
  rw [lieBracket]
  -- In End(ℝ³), `*` is definitionally `∘ₗ`
  have h := hatMap_commutator v w
  -- h: hatMap v ∘ₗ hatMap w - hatMap w ∘ₗ hatMap v = hatMap (crossProd v w)
  -- Goal: hatMap (crossProd v w) = hatMap v * hatMap w - hatMap w * hatMap v
  -- Since A * B = A ∘ₗ B, the goal is the same as h.symm
  -- In End(ℝ³), A * B = A ∘ₗ B by definition
  -- So hatMap v * hatMap w = hatMap v ∘ₗ hatMap w
  -- Therefore h.symm gives exactly the goal
  exact h.symm

/-! ### SO(3) action on ℝ³

The defining action of SO(3) on ℝ³ is by rotation. The corresponding Lie algebra action
is the hat map: an element `v ∈ ℝ³ ≅ so(3)` acts on `w ∈ ℝ³` by `v × w`.
-/

/-- The defining representation of `so(3)` on `ℝ³`: `v` acts as `w ↦ v × w`. -/
def so3_action_R3 : ℝ³ →ₗ[ℝ] (ℝ³ →ₗ[ℝ] ℝ³) := hatMap

/-- The infinitesimal rotation around the x-axis acts on a vector `w` as `(1,0,0) × w`. -/
@[simp] lemma so3_action_x (w : ℝ³) : so3_action_R3 angularMomentumX w = crossProd angularMomentumX w := rfl

/-- The infinitesimal rotation around the y-axis. -/
@[simp] lemma so3_action_y (w : ℝ³) : so3_action_R3 angularMomentumY w = crossProd angularMomentumY w := rfl

/-- The infinitesimal rotation around the z-axis. -/
@[simp] lemma so3_action_z (w : ℝ³) : so3_action_R3 angularMomentumZ w = crossProd angularMomentumZ w := rfl

end SO3
