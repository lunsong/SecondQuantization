import Mathlib.Tactic

namespace SecondQuantization

variable (α R : Type) [CommRing R]

abbrev Operator := (Finset α → R) →ₗ[R] (Finset α → R)

@[ext]
theorem Operator.ext {A B : Operator α R} : (∀ φ, A φ = B φ) → A = B := LinearMap.ext

instance Operator.semiring : Ring (Operator α R) :=
  inferInstanceAs (Ring ((Finset α → R) →ₗ[R] (Finset α → R)))

--instance Operator.algebra : Algebra R (Operator α R) :=
--  inferInstanceAs (Algebra R ((Finset α → R) →ₗ[R] (Finset α → R)))

variable {α} [LinearOrder α]

namespace Fermion

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

def ann (x : α) : Operator α R where
  toFun φ s := 
    if x ∉ s then
      if Even (Finset.card {y ∈ s | y < x}) then
        φ (insert x s)
      else
        - φ (insert x s)
    else 0
  map_smul' a φ := by
    ext s
    simp
  map_add' φ ψ := by
    ext s
    simp only [Pi.add_apply, neg_add_rev]
    split_ifs
    · rw [add_zero]
    · rfl
    · rw [add_comm]

theorem cre_ann {x y : α} : cre R x * ann R y + ann R y * cre R x = if x = y then 1 else 0 := by
  split_ifs with h
  · cases h
    ext φ s
    simp only [cre, ann, ite_not, LinearMap.add_apply, Module.End.mul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      Finset.mem_insert, true_or, Finset.erase_insert_eq_erase, Pi.add_apply, Module.End.one_apply]
    split
    · rename_i hx
      let S : Finset α := {y ∈ s | y < x}
      let S' : Finset α := {y ∈ s.erase x | y < x}
      have : S' = S := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, and_congr_left_iff,
          and_iff_right_iff_imp, S', S]
        exact fun h _ => h.ne
      have : Even S.card ↔ Even S'.card := by simp [this]
      split_ifs with h₁ h₂ h₃
      any_goals simp only [Finset.insert_erase hx, neg_neg, add_zero]
      · exact (h₂ (this.mp h₁)).elim
      · exact (h₁ (this.mpr h₃)).elim
    · rename_i hx
      let S : Finset α := {y ∈ s | y < x}
      let S' : Finset α := {y ∈ insert x s | y < x}
      have : S' = S := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, and_congr_left_iff, or_iff_right_iff_imp,
          S', S]
        exact fun h h' => (h.ne h').elim
      have : Even S.card ↔ Even S'.card := by simp [this]
      split_ifs with h₁ h₂ h₃
      any_goals simp only [Finset.erase_eq_of_notMem hx, neg_neg, zero_add]
      · exact (h₂ (this.mp h₁)).elim
      · exact (h₁ (this.mpr h₃)).elim
  · ext φ s
    simp only [cre, ann, ite_not, LinearMap.add_apply, Module.End.mul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Finset.mem_erase, ne_eq, Ne.symm h, not_false_eq_true, true_and,
      Finset.mem_insert, h, false_or, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply]
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · simp [hx, hy]
      · have hins_erase : insert y (s.erase x) = (insert y s).erase x := by
          rw [Finset.erase_insert_of_ne (Ne.symm h)]
        simp only [if_pos hx, if_neg hy, hins_erase]
        set A : Finset α := {z ∈ s | z < x} with hA_def
        set B : Finset α := {z ∈ s.erase x | z < y} with hB_def
        set C : Finset α := {z ∈ s | z < y} with hC_def
        set D : Finset α := {z ∈ insert y s | z < x} with hD_def
        have key : (Even A.card ↔ Even D.card) ↔ ¬ (Even B.card ↔ Even C.card) := by
          rcases lt_or_gt_of_ne h with hxy | hxy
          · have hDA : D = A := by
              ext a
              simp only [D, A, Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨h₁ | h₁, h₂⟩
                · exact absurd (h₁ ▸ h₂) (not_lt_of_gt hxy)
                · exact ⟨h₁, h₂⟩
              · rintro ⟨h₁, h₂⟩; exact ⟨Or.inr h₁, h₂⟩
            have hBC : B = C.erase x := by
              ext a
              simp only [B, C, Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩
              · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩
            have hx_in_C : x ∈ C := by
              simp only [C, Finset.mem_filter]; exact ⟨hx, hxy⟩
            rw [hDA, hBC, Finset.card_erase_of_mem hx_in_C]
            have hCne : C.card ≠ 0 := by
              intro h0
              rw [Finset.card_eq_zero] at h0
              rw [h0] at hx_in_C
              exact (Finset.notMem_empty _) hx_in_C
            rw [Nat.even_sub (Nat.one_le_iff_ne_zero.mpr hCne)]
            have : ¬ Even 1 := by decide
            tauto
          · have hBC : B = C := by
              ext a
              simp only [B, C, Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨⟨_, h₂⟩, h₃⟩; exact ⟨h₂, h₃⟩
              · rintro ⟨h₁, h₂⟩
                refine ⟨⟨?_, h₁⟩, h₂⟩
                rintro rfl; exact absurd h₂ (not_lt_of_gt hxy)
            have hDA : D = insert y A := by
              ext a
              simp only [D, A, Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨h₁ | h₁, h₂⟩
                · exact Or.inl h₁
                · exact Or.inr ⟨h₁, h₂⟩
              · rintro (rfl | ⟨h₁, h₂⟩)
                · exact ⟨Or.inl rfl, hxy⟩
                · exact ⟨Or.inr h₁, h₂⟩
            have hy_notin_A : y ∉ A := by
              simp only [A, Finset.mem_filter]; rintro ⟨h₁, _⟩; exact hy h₁
            rw [hBC, hDA, Finset.card_insert_of_notMem hy_notin_A, Nat.even_add_one]
            tauto
        by_cases hA : Even A.card <;> by_cases hB : Even B.card <;>
          by_cases hC : Even C.card <;> by_cases hD : Even D.card <;>
          (try { exfalso; tauto }) <;>
          simp only [hA, hB, hC, hD, ↓reduceIte, neg_neg] <;>
          ring
    · simp [hx]
    
      


end Fermion

end SecondQuantization
