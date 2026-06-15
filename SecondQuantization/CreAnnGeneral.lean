import Mathlib.Tactic

namespace Fermion

variable (α R : Type) [CommRing R]

abbrev Operator := (Finset α → R) →ₗ[R] (Finset α → R)

variable {α} [LinearOrder α]

def commSign (s : Finset α) (a : α) : ℝ :=
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
  toFun φ s := 
    if x ∈ s then
      if Even (Finset.card {y ∈ s | y < x}) then
        φ (s.erase x)
      else
        - φ (s.erase x)
    else 0
  map_smul' a φ := by
    ext s
    simp
  map_add' φ ψ := by
    ext s
    simp only [Pi.add_apply, neg_add_rev]
    split_ifs
    · rfl
    · rw [add_comm]
    · rw [add_zero]

end Fermion
