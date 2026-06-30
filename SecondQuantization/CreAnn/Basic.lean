import Mathlib.Tactic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

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

end Fermion

