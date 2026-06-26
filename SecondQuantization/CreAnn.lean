import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace Fermion

variable (α R : Type) [RCLike R]

open scoped ComplexOrder

abbrev Operator := (Finset α → R) →L[R] (Finset α → R)

variable {α} [LinearOrder α]

def commSign (s : Finset α) (a : α) : ℤ :=
  if Even (Finset.filter (· < a) s).card then 1 else -1

theorem commSign_range {α : Type} [LinearOrder α] (s : Finset α) (a : α) :
    commSign s a = 1 ∨ commSign s a = -1 := by
  unfold commSign
  split_ifs <;> tauto

theorem commSign_erase {α : Type} [LinearOrder α] (s : Finset α) (a b : α) :
    commSign (s.erase a) b = if a < b ∧ a ∈ s then -commSign s b else commSign s b := by
  unfold commSign
  have : Finset.filter (· < b) (s.erase a) = (Finset.filter (· < b) s).erase a := by
    ext x; simp; tauto
  rw [this, Finset.card_erase_eq_ite]
  split_ifs <;> grind
  
theorem commSign_insert {α : Type} [LinearOrder α] (s : Finset α) (a b : α) :
    commSign (insert a s) b = if a < b ∧ a ∉ s then -commSign s b else commSign s b := by
  unfold commSign
  have : Finset.card {x ∈ insert a s | x < b} =
   if a < b ∧ a ∉ s then Finset.card {x ∈ s | x < b} + 1 else Finset.card {x ∈ s | x < b} := by
    split_ifs with h
    · trans Finset.card (insert a {x ∈ s | x < b})
      · congr; ext x; grind
      · rw [Finset.card_insert_of_notMem]; grind
    · congr 1; ext x; grind
  rw [this]
  split_ifs <;> grind

def cre (x : α) : Operator α R where
  toFun φ s := if x ∈ s then commSign s x * φ (s.erase x) else 0
  map_smul' a φ := by ext s; simp [commSign]
  map_add' φ ψ := by
    ext s
    simp only [commSign, Int.reduceNeg, Int.cast_ite, Int.cast_one, Int.cast_neg, Pi.add_apply,
      ite_mul, one_mul, neg_mul, neg_add_rev]
    grind

@[continuity]
theorem continuous_ite_left {c : Prop} [Decidable c] {β : Type} [TopologicalSpace β] {x : β} :
    Continuous (ite c x) := by
  by_cases h : c
  · rw [show ite c x = fun _ => x by ext; simp [h]]
    exact continuous_const
  · rw [show ite c x = id by ext; simp [h]]
    exact continuous_id

def ann (x : α) : Operator α R where
  toFun φ s := if x ∉ s then commSign s x * φ (insert x s) else 0
  map_smul' a φ := by ext s; simp[commSign]
  map_add' φ ψ := by
    ext s
    simp only [commSign, Int.reduceNeg, Int.cast_ite, Int.cast_one, Int.cast_neg, Pi.add_apply,
      ite_mul, one_mul, neg_mul, neg_add_rev, ite_not]
    grind

variable {R}

set_option linter.flexible false in
theorem cre_ann {x y : α} : cre R x * ann R y + ann R y * cre R x = if x = y then 1 else 0 := by
  ext φ s
  simp [cre, ann, commSign_erase, commSign_insert]
  split_ifs
  any_goals simp
  any_goals grind
  any_goals
    rename_i h
    rw [Finset.erase_insert_of_ne (Ne.symm h)]
    ring
  · rename_i h h'
    rw [h', Finset.insert_erase h]
    rcases commSign_range s y with h | h <;> simp [h]
  · rename_i h1 h2 h3 h4 h5
    rw [h5, Finset.erase_insert h2]
    rcases commSign_range s y with h | h <;> simp [h]

set_option linter.flexible false in
theorem cre_cre {x y : α} : cre R x * cre R y + cre R y * cre R x = 0 := by
  ext φ s
  simp [cre, commSign_erase, Finset.erase_right_comm]
  split_ifs
  any_goals simp
  any_goals grind


set_option linter.flexible false in
theorem ann_ann {x y : α} : ann R x * ann R y + ann R y * ann R x = 0 := by
  ext φ s
  simp [ann, commSign_insert, Finset.insert_comm]
  split_ifs
  any_goals simp
  any_goals grind

instance [Fintype α] : NormedAlgebra ℚ (Operator α R →L[R] Operator α R) where
  norm_smul_le _ _ := ContinuousLinearMap.opNorm_smul_le _ _

instance [Fintype α] : CompleteSpace (Operator α R →L[R] Operator α R) :=
  FiniteDimensional.complete R (Operator α R →L[R] Operator α R)

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator

--instance : CompleteSpace (Matrix ι ι R) := FiniteDimensional.complete R (Matrix ι ι R)

--def mulLeft : Operator α R →L[R] Operator α R →L[R] Operator α R := by


set_option maxHeartbeats 0 in
theorem exp_adj [Fintype α] (A : Operator α R)
  (x : ι → Operator α R) (K : Matrix ι ι R)
  (h : ∀ i, A * x i - x i * A = ∑ j, K i j • x j) :
    ∀ i, NormedSpace.exp A * x i * NormedSpace.exp (-A) = ∑ j, (NormedSpace.exp K) i j • x j := by
  let A_left := ContinuousLinearMap.mulLeftRight R (Operator α R) A 1
  let A_right := ContinuousLinearMap.mulLeftRight R (Operator α R) 1 (-A)
  have commute_A_left_A_right : Commute A_left A_right := by
    ext X φ s
    simp [A_left, A_right]
  have := NormedSpace.exp_add_of_commute commute_A_left_A_right
  have A_left_pow (n : ℕ) : A_left ^ n = ContinuousLinearMap.mulLeftRight R (Operator α R) (A ^ n) 1 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      ext X φ s
      simp [A_left]
  have A_right_pow (n : ℕ) : A_right ^ n = ContinuousLinearMap.mulLeftRight R (Operator α R) 1 ((-A) ^ n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      ext X φ s
      simp only [ContinuousLinearMap.coe_mul, Function.comp_apply, ContinuousLinearMap.mulLeftRight_apply, one_mul, A_right]
      apply congr_fun
      congr 1
      change (-A * (-A) ^ n) φ = ((-A) ^ n * -A) φ
      congr 1
      trans (-A) ^ (n + 1)
      · rw [add_comm, pow_add, pow_one]
      · rw [pow_succ]
  have exp_A_left : NormedSpace.exp A_left = ContinuousLinearMap.mulLeftRight R (Operator α R) (NormedSpace.exp A) 1 := by
    rw [NormedSpace.exp_eq_tsum R]
    simp only [A_left_pow]
    apply HasSum.tsum_eq
    simp only [HasSum, SummationFilter.unconditional_filter]
    conv =>
      arg 1
      equals (fun x ↦ ContinuousLinearMap.mulLeftRight R (Operator α R) x 1) ∘ (fun s ↦ ∑ x ∈ s, (x.factorial : R)⁻¹ • A ^ x) =>
        apply funext
        intro s
        simp only [Function.comp_apply, map_sum, map_smul, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply,
          Pi.smul_apply]
    apply Filter.Tendsto.comp (y := nhds (NormedSpace.exp A))
    · change ContinuousAt (fun x ↦ ((ContinuousLinearMap.mulLeftRight R (Operator α R)) x) 1) (NormedSpace.exp A)
      apply Continuous.continuousAt
      conv =>
        arg 1
        equals (fun x ↦ x 1) ∘ ContinuousLinearMap.mulLeftRight R (Operator α R) =>
          apply funext
          intro x
          simp
      apply Continuous.comp
      · apply Continuous.clm_apply
        · apply continuous_id'
        · apply continuous_const
      exact (ContinuousLinearMap.mulLeftRight R (Operator α R)).cont
    exact NormedSpace.exp_series_hasSum_exp' A

  have exp_A_right : NormedSpace.exp A_right = ContinuousLinearMap.mulLeftRight R (Operator α R) 1 (NormedSpace.exp (-A)) := by
    rw [NormedSpace.exp_eq_tsum R]
    simp only [A_right_pow]
    apply HasSum.tsum_eq
    simp only [HasSum, SummationFilter.unconditional_filter]
    conv =>
      arg 1
      equals (fun x ↦ ContinuousLinearMap.mulLeftRight R (Operator α R) 1 x) ∘ (fun s ↦ ∑ x ∈ s, (x.factorial : R)⁻¹ • (-A) ^ x) =>
        apply funext
        intro s
        simp only [Function.comp_apply, map_sum, map_smul]
    apply Filter.Tendsto.comp (y := nhds (NormedSpace.exp (-A)))
    · change ContinuousAt (fun x ↦ ((ContinuousLinearMap.mulLeftRight R (Operator α R)) 1) x) (NormedSpace.exp (-A))
      apply Continuous.continuousAt
      exact (ContinuousLinearMap.mulLeftRight R (Operator α R) 1).cont
    exact NormedSpace.exp_series_hasSum_exp' (-A)
  have ad_pow (n : ℕ) : ∀ i, ((A_left + A_right) ^ n) (x i) = ∑ j, (K ^ n) i j • x j := by
    induction n with
    | zero => simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      rw [pow_succ, ContinuousLinearMap.mul_apply]
      conv_lhs =>
        arg 2
        simp [A_left, A_right, ← sub_eq_add_neg, h]
      rw [map_sum]
      conv_lhs =>
        arg 2; intro j
        rw [map_smul, ih, Finset.smul_sum]
        arg 2; intro k
        rw [smul_smul]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; intro j
        rw [← Finset.sum_smul]
        change (K * K ^ n) i j • x j
      rw [add_comm, pow_add, pow_one]
  have exp_ad : ∀ i, NormedSpace.exp (A_left + A_right) (x i) = ∑ j, NormedSpace.exp K i j • x j := by
    intro i
    simp only [NormedSpace.exp_eq_tsum R]
    trans ∑' (n : ℕ), (n.factorial : R)⁻¹ • ((A_left + A_right) ^ n) (x i)
    · apply Eq.symm
      apply HasSum.tsum_eq
      simp only [HasSum, SummationFilter.unconditional_filter]
      conv =>
        arg 1
        equals (fun M ↦ M (x i)) ∘ (fun s ↦ ∑ n ∈ s, (n.factorial : R)⁻¹ • (A_left + A_right) ^ n) =>
          apply funext
          intro s
          simp
      apply Filter.Tendsto.comp (y := nhds (NormedSpace.exp (A_left + A_right)))
      · simp only [NormedSpace.exp_eq_tsum R]
        change ContinuousAt _ _
        apply Continuous.continuousAt
        apply Continuous.eval_const
        exact continuous_id
      exact NormedSpace.exp_series_hasSum_exp' _
    · conv =>
        arg 1; arg 1; intro n
        rw [ad_pow, Finset.smul_sum]
      apply HasSum.tsum_eq
      simp only [HasSum, SummationFilter.unconditional_filter]
      conv =>
        arg 1
        equals (fun K' ↦ ∑ j, K' i j • x j) ∘ (fun s ↦ ∑ n ∈ s, (n.factorial : R)⁻¹ • K ^ n) =>
          apply funext
          intro s
          rw [Finset.sum_comm]
          congr
          apply funext
          intro j
          conv_lhs =>
            arg 2; intro k
            rw [smul_smul]
          rw [← Finset.sum_smul]
          simp only
          congr
          trans (∑ n ∈ s, (n.factorial : R)⁻¹ • (K ^ n) i) j
          · apply Eq.symm
            apply Finset.sum_apply
          · apply congrFun
            apply Eq.symm
            apply Finset.sum_apply
      apply Filter.Tendsto.comp (y := nhds (NormedSpace.exp K))
      · simp only [NormedSpace.exp_eq_tsum R]
        change ContinuousAt _ _
        apply Continuous.continuousAt
        simp_all only [map_neg, Commute.neg_right_iff, A_left, A_right]
        apply continuous_finset_sum
        intro i_1 a
        simp_all only [Finset.mem_univ]
        apply Continuous.smul
        · change Continuous ((fun x ↦ x i_1) ∘ (fun (x : Matrix ι ι R) ↦ x i))
          apply Continuous.comp
          · apply continuous_apply
          · apply continuous_apply
        · apply continuous_const
      exact NormedSpace.exp_series_hasSum_exp' (𝕂 := R) K

  intro i
  have key : (NormedSpace.exp (A_left + A_right)) (x i) =
      NormedSpace.exp A * x i * NormedSpace.exp (-A) := by
    rw [this, exp_A_left, exp_A_right]
    simp only [ContinuousLinearMap.coe_mul, Function.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one, mul_assoc]
  rw [← key, exp_ad]

end


end Fermion

