import SecondQuantization.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Batteries.Tactic.Trans

namespace HatreeFock

open Fock

variable {α : Type} [LinearOrder α]

/-- An operator is creLike if it's a sum of creation operators -/
def creLike (x : Operator α) : Prop := ∃ f : α →₀ ℝ, x = f.sum fun a k ↦ k • cre a

/-- An operator is annLike if it's a sum of annihilation operators -/
def annLike (x : Operator α) : Prop := ∃ f : α →₀ ℝ, x = f.sum fun a k ↦ k • ann a

omit [LinearOrder α] in
/-- The star of a annLike operator is creLike -/
theorem creLike_star (x : Operator α) : creLike (star x) ↔ annLike x := by
  constructor
  · intro h
    rw[←star_star x]
    generalize star x = x' at *
    obtain ⟨f, hf⟩ := h
    use f
    rw[hf]
    conv_lhs =>
      rw[←starₗ_apply, Finsupp.sum, map_sum]
      arg 2; intro a
      rw[map_smul, starₗ_apply, star_cre]
    rfl
  · intro h
    obtain ⟨f, hf⟩ := h
    use f
    rw[← starₗ_apply, hf, Finsupp.sum, map_sum]
    conv_lhs =>
      arg 2
      intro a
      rw[map_smul, starₗ_apply, star_ann]
    rfl

omit [LinearOrder α] in
/-- The star of a creLike operator is annLike -/
theorem annLike_star (x : Operator α) : annLike (star x) ↔ creLike x := by
  conv_rhs =>
    rw[←star_star x]
  exact (creLike_star _).symm

omit [LinearOrder α] in
theorem commutator_sum {β : Type} (s₁ s₂ : Finset β) (f₁ f₂ : β → Operator α) : 
    [ ∑ i ∈ s₁, f₁ i, ∑ i ∈ s₂, f₂ i]ₐ = ∑ i ∈ s₁, ∑ j ∈ s₂, [f₁ i, f₂ j]ₐ := by
  rw[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := s₂), ←Finset.sum_add_distrib]
  conv_lhs =>
    arg 2
    intro i
    rw[←Finset.sum_add_distrib]

/-- The anti-commutation rule between creation and annihilation operators, using if-then-else -/
theorem ann_cre' (a b : α) : [ann a, cre b]ₐ = if a = b then 1 else 0 := by
  split
  · rename_i h
    rw[h, ann_cre]
    exact sub_add_cancel _ _
  · rename_i h
    rw[ann_cre_ne _ _ h]
    exact neg_add_cancel _

set_option synthInstance.maxHeartbeats 30000 in
-- necessary for proof
/-- The anti-commutator between an annLike operator and a creLike operator is a real number -/
theorem annLike_creLike_commutator (x y : Operator α) :
    annLike x → creLike y → ∃ r : ℝ, [x, y]ₐ = Operator.ofReal r := by
  intro ⟨f, hf⟩ ⟨g, hg⟩
  rw[Finsupp.sum] at hf hg
  rw[hf, hg, commutator_sum]
  have smul_one' (r : ℝ) : r • (1 : Operator α) = Operator.ofReal r := by
    rw[Algebra.smul_def, mul_one]
  conv =>
    arg 1; intro r;
    conv =>
      arg 1; arg 2; intro i
      conv =>
        arg 2; intro j
        rw[smul_mul_smul, smul_mul_smul, mul_comm (g j), ←smul_add, ann_cre', smul_ite,
          smul_zero, smul_one']
      rw[Finset.sum_ite_eq, ← Finsupp.mul_apply]
    rw[Finset.sum_ite_mem]
    tactic =>
      have : f.support ∩ g.support = (f*g).support := by
        ext x
        simp
    rw[this, ← map_sum]
  use (f*g).sum fun i v ↦ v
  rfl

/-- For an annLike operator a, the vacuum expectation of x * a is zero for any x -/
theorem vacExpect_mul_annLike (x a : Operator α) : annLike a → vacExpect (x * a) = 0 := by
  intro ⟨f, hf⟩
  rw[hf,Finsupp.sum, Finset.mul_sum, map_sum]
  conv_lhs =>
    arg 2; intro i
    rw[mul_smul_comm, map_smul, vacExpect_mul_ann, smul_zero]
  rw[Finset.sum_const_zero]

/-- For an creLike operator a, the vacuum expectation of a * x  is zero for any x -/
theorem vacExpect_creLike_mul (a x : Operator α) : creLike a → vacExpect (a * x) = 0 := by
  intro h
  rw[←annLike_star] at h
  rw[←vacExpect_star, star_mul]
  exact vacExpect_mul_annLike _ _ h

/-- The anti-commutator between an annLike operator x and a creLike operator y is a real number,
and is equal to the expectation value of x * y -/
theorem annLike_creLike_commutator' (x y : Operator α) (hx : annLike x) (hy : creLike y) :
    [x, y]ₐ = Operator.ofReal (vacExpect (x * y)) := by
  have : [x, y]ₐ = Operator.ofReal (vacExpect [x, y]ₐ) := by
    have ⟨r, hr⟩ := annLike_creLike_commutator x y hx hy
    rw[hr, vacExpect_ofReal]
  rw[this]
  congr 1
  rw[map_add, vacExpect_mul_annLike _ _ hx, add_zero]

/-- The vacuum expectation of 1 is 1 -/
theorem vacExpect_one : vacExpect (1 : Operator α) = 1 := by
  rw[show (1 : Operator α) = Operator.ofReal 1 from rfl, vacExpect_ofReal]

omit [LinearOrder α] in
theorem sum_fin_add {n : ℕ} (f : Fin (n + 1) → Operator α) :
    ∑ i : Fin (n + 1), f i = f 0  + (∑ i : Fin n, f i.succ) := by
  let s : Finset (Fin (n + 1)) := {0}
  rw[← Finset.sum_add_sum_compl s, Finset.sum_singleton]
  congr 1
  apply Eq.symm
  refine Finset.sum_of_injOn Fin.succ ?_ ?_ ?_ ?_
  · simp
  · simp[s]
  · simp +contextual [s]
  · simp

set_option maxHeartbeats 300000 in
-- it's necessary
omit [LinearOrder α] in
/-- The (normal or anti) commutator between an operator and a product of operators.
x a₁ a₂ ⋯ aₙ = (-1)ⁿ a₁ a₂ ⋯ aₙ x + ∑ i, (-1)ⁱ (a₁ ⋯ aᵢ₋₁) {x, aᵢ} (aᵢ₊₁ ⋯ aₙ) -/
theorem commutator_prod (x : Operator α) (L : List (Operator α)) :
  x * L.prod - (-1)^L.length • (L.prod * x) =
    ∑ i : Fin L.length, (-1)^i.val • ((L.take i).prod * [x, L.get i]ₐ * (L.drop (i+1)).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    trans [x, a]ₐ * L.prod  - a * (x * L.prod - (-1)^L.length • (L.prod * x))
    · simp[add_mul, mul_sub, pow_add, -zsmul_eq_mul]
      ac_nf
      rw[←sub_add, add_sub_cancel_right]
    simp only [List.length_cons]
    rw[sum_fin_add]
    conv_rhs =>
      conv =>
        arg 1
        simp
      conv =>
        arg 2
        simp[pow_add, -zsmul_eq_mul, -List.get_eq_getElem, List.get_cons_succ']
        conv =>
          arg 1; arg 2; intro i
          simp only [mul_assoc]
          rw[←mul_smul_comm]
          simp only [← mul_assoc]
        rw[← Finset.mul_sum, ← ih]
    rw[← sub_eq_add_neg]

/-- The (normal or anti) commutator between an annLike operator and a product of creLike operators.
x a₁ a₂ ⋯ aₙ = (-1)ⁿ a₁ a₂ ⋯ aₙ x + ∑ i, (-1)ⁱ {x, aᵢ} (a₁ ⋯ aᵢ₋₁ aᵢ₊₁ ⋯ aₙ) -/
theorem commutator_annLike_mul_prod_creLike (x : Operator α) (L : List (Operator α))
  (hx : annLike x) (hL : ∀ l ∈ L, creLike l) :
  x * L.prod - (-1)^L.length • (L.prod * x) = 
    ∑ i : Fin L.length, (-1)^i.val • vacExpect (x * L.get i) • (L.eraseIdx i).prod := by
  rw[commutator_prod]
  conv_lhs =>
    arg 2
    intro i
    tactic =>
      have creLike_Li : creLike (L.get i) := hL _ (List.get_mem _ _)
      have := annLike_creLike_commutator' _ _ hx creLike_Li
    rw[this, Operator.ofReal, mul_assoc, ←Algebra.smul_def, mul_smul_comm,← List.prod_append,
      ←List.eraseIdx_eq_take_drop_succ]


section 

variable (L₁ L₂ : List (Operator α))

/-- The commutator matrix for annLike operators : Mᵢⱼ = {cᵢ†, dⱼ} -/
noncomputable def commutatorMatrix : Matrix (Fin L₁.length) (Fin L₂.length) ℝ := Matrix.of <|
  fun i j ↦  vacExpect (star (L₁.get i) * L₂.get j) 

variable (n : ℕ) (hn₁ : n = L₁.length) (hn₂ : n = L₂.length)

/-- When the number of operators are equal, the commutator matrix is a square matrix -/
noncomputable def commutatorMatrix_sqr :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of <|
  fun i ↦ (commutatorMatrix L₁ L₂ (i.cast hn₁)) ∘ Fin.cast hn₂

set_option maxHeartbeats 300000 in
-- necessary
set_option synthInstance.maxHeartbeats 30000 in
-- necessary
/-- ⟨ (c₁ c₂ ⋯ cₙ)† (d₁ d₂ ⋯ dₙ) ⟩ = det [{cᵢ†, dⱼ}] -/
theorem vacExpect_star_prod_annLike_mul_prod_annLike
  (h₁ : ∀ x ∈ L₁, creLike x) (h₂ : ∀ x ∈ L₂, creLike x) :
    vacExpect (star L₁.prod * L₂.prod) = (commutatorMatrix_sqr L₁ L₂ n hn₁ hn₂).det := by
  revert L₁ L₂
  induction n with
  | zero =>
    intro _ _ hn₁ hn₂ _ _
    have hn₁ := List.length_eq_zero_iff.mp hn₁.symm
    have hn₂ := List.length_eq_zero_iff.mp hn₂.symm
    simp[hn₁, hn₂, vacExpect_one]
  | succ n ih =>
    intro L₁ L₂ hn₁ hn₂ h₁ h₂
    have ⟨x, L₁',hx⟩ := List.exists_of_length_succ _ hn₁.symm
    conv_lhs =>
      arg 2; arg 1
      rw[hx]
      change star (x * L₁'.prod) 
      rw[star_mul]
    have hx' : annLike (star x) := by
      rw[annLike_star]
      apply h₁
      rw[hx]
      exact List.mem_cons_self
    trans vacExpect (star L₁'.prod * (star x * L₂.prod - (-1)^L₂.length • (L₂.prod * star x)))
    · simp only [mul_sub, map_sub, zsmul_eq_mul, ← mul_assoc]
      apply Eq.symm
      rw[sub_eq_self, vacExpect_mul_annLike _ _ hx']
    rw[commutator_annLike_mul_prod_creLike _ _ hx' h₂, Finset.mul_sum, map_sum]
    have hn₁' : L₁'.length = n := by
      rw[hx, List.length_cons, add_left_inj] at hn₁
      exact hn₁.symm
    have hn₂' (i : Fin L₂.length) : (L₂.eraseIdx i).length = n := by
      rw[List.length_eraseIdx]
      simp[←hn₂]
      rw[hn₂]
      exact i.isLt
    have h₁' : ∀ l ∈ L₁', creLike l := by
      intro l hl
      apply h₁
      rw[hx, List.mem_cons]
      exact Or.inr hl
    have h₂' (i : Fin L₂.length) : ∀ l ∈ L₂.eraseIdx i, creLike l := by
      intro l hl
      apply h₂
      rw[←List.insertIdx_eraseIdx_getElem i.isLt, List.mem_insertIdx]
      exact Or.inr hl
      simp[List.length_eraseIdx]
      omega
    conv =>
      lhs
      arg 2
      intro i
      rw[mul_smul_comm, mul_smul_comm, zsmul_eq_mul]
      tactic =>
        have : (((-1) ^ i.val : ℤ) : Operator α) = Operator.ofReal ((-1)^i.val : ℝ) := by simp
      rw[this, ← Algebra.smul_def, map_smul, map_smul]
      tactic =>
      rw[ih _ _ hn₁'.symm (hn₂' i).symm h₁' (h₂' i)]
    have : NeZero L₁.length := NeZero.mk (by simp[←hn₁])
    have : NeZero L₂.length := NeZero.mk (by simp[←hn₂])
    rw[show x = L₁.get 0 by simp[hx]]
    have (i : Fin (n + 1)) :
      vacExpect (star (L₁.get 0) * L₂.get (i.cast hn₂)) =
        commutatorMatrix_sqr L₁ L₂ (n + 1) hn₁ hn₂ 0 i := by rfl
    trans ∑ i : Fin (n + 1),
      (-1) ^ (i.cast hn₂).val • vacExpect (star (L₁.get 0) * L₂.get (i.cast hn₂))
        • (commutatorMatrix_sqr L₁' (L₂.eraseIdx ↑i) n hn₁'.symm (hn₂' (i.cast hn₂)).symm).det
    · apply Eq.symm
      refine Finset.sum_of_injOn (Fin.cast hn₂) ?_ ?_ ?_ ?_
      · simp
      · simp
      · intro i hi hc
        simp at hc
        specialize hc (i.cast hn₂.symm)
        simp at hc
      · simp
    conv_lhs =>
      arg 2
      intro i
      rw[this]
      simp
      rw[←mul_assoc]
    conv_rhs =>
      rw[Matrix.det_succ_row _ 0]
      simp
    congr
    ext i
    congr 2
    ext j k
    simp[commutatorMatrix_sqr, commutatorMatrix, hx]
    congr 2
    rw[List.getElem_eraseIdx, Fin.succAbove]
    obtain ⟨i, hi⟩ := i
    obtain ⟨k, hk⟩ := k
    by_cases h : k < i
    · simp[h]
    · simp[h]


end

end HatreeFock
