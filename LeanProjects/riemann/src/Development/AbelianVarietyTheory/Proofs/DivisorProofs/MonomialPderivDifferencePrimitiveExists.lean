import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem monomial_pderiv_difference_primitive (n : ℕ) (i i' : Fin (n + 1)) (hii : i ≠ i') :
    ∀ b : ℕ, ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ), α i' = b →
    ∃ J₁ R : MvPolynomial (Fin (n + 1)) ℝ, pderiv i' J₁ - pderiv i J₁ = monomial α c ∧
      J₁ = (-(1 / ((α i : ℝ) + 1))) • (X i * monomial α c) + R ∧
      ∀ β ∈ R.support, β i' < α i' ∧ ∀ j, j ≠ i → j ≠ i' → β j = α j := by
  have hXm : ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ),
      X i * monomial α c = monomial (α + Finsupp.single i 1) c := by
    intro α c
    rw [X, monomial_mul, one_mul, add_comm (Finsupp.single i 1) α]
  have hpi : ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ),
      pderiv i (monomial (α + Finsupp.single i 1) c) = monomial α (c * ((α i : ℝ) + 1)) := by
    intro α c
    rw [pderiv_monomial]
    simp
  have hpi' : ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ),
      pderiv i' (monomial (α + Finsupp.single i 1) c)
        = monomial (α + Finsupp.single i 1 - Finsupp.single i' 1) (c * (α i' : ℝ)) := by
    intro α c
    rw [pderiv_monomial]
    simp [Finsupp.single_apply, hii]
  have hsplit : ∀ x y : MvPolynomial (Fin (n + 1)) ℝ,
      pderiv i' (x + y) - pderiv i (x + y) = (pderiv i' x - pderiv i x) + (pderiv i' y - pderiv i y) := by
    intro x y
    simp only [map_add]
    abel
  intro b
  induction b with
  | zero =>
    intro α c hb
    refine ⟨(-(1 / ((α i : ℝ) + 1))) • (X i * monomial α c), 0, ?_, by simp, by simp⟩
    have ha : ((α i : ℝ) + 1) ≠ 0 := by positivity
    rw [hXm, Derivation.map_smul, Derivation.map_smul, hpi, hpi', hb, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul]
    have e2 : -(1 / ((α i : ℝ) + 1)) * (c * ((α i : ℝ) + 1)) = -c := by field_simp
    rw [e2]
    simp
  | succ b ih =>
    intro α c hb
    have ha : ((α i : ℝ) + 1) ≠ 0 := by positivity
    set α' := α + Finsupp.single i 1 - Finsupp.single i' 1 with hα'
    have hα'i' : α' i' = b := by
      simp [hα', Finsupp.single_apply, hii, hb]
    have hα'j : ∀ j, j ≠ i → j ≠ i' → α' j = α j := by
      intro j h1 h2
      simp [hα', Finsupp.single_apply, Ne.symm h1, Ne.symm h2]
    obtain ⟨J', R', hD', hJ', hR'⟩ := ih α' (c * ((b : ℝ) + 1) / ((α i : ℝ) + 1)) hα'i'
    refine ⟨(-(1 / ((α i : ℝ) + 1))) • (X i * monomial α c) + J', J', ?_, rfl, ?_⟩
    · rw [hsplit, hD', hXm, Derivation.map_smul, Derivation.map_smul, hpi, hpi', hb, smul_monomial, smul_monomial,
        smul_eq_mul, smul_eq_mul]
      have e1 : -(1 / ((α i : ℝ) + 1)) * (c * ((b + 1 : ℕ) : ℝ)) + c * ((b : ℝ) + 1) / ((α i : ℝ) + 1) = 0 := by
        push_cast; field_simp; ring
      have e2 : -(1 / ((α i : ℝ) + 1)) * (c * ((α i : ℝ) + 1)) = -c := by field_simp
      rw [e2, map_neg, sub_neg_eq_add, add_comm _ (monomial α c), add_assoc, ← map_add, e1, map_zero, add_zero]
    · intro β hβ
      rw [hJ', hXm, smul_monomial] at hβ
      rcases Finset.mem_union.1 (support_add hβ) with h | h
      · have hb' := support_monomial_subset h
        rw [Finset.mem_singleton] at hb'
        subst hb'
        refine ⟨?_, fun j hj hj' => ?_⟩
        · simp [Finsupp.single_apply, hii, hα'i', hb]
        · simp [Finsupp.single_apply, Ne.symm hj, hα'j j hj hj']
      · obtain ⟨h1, h2⟩ := hR' β h
        rw [hα'i'] at h1
        exact ⟨by omega, fun j hj hj' => (h2 j hj hj').trans (hα'j j hj hj')⟩

theorem monomial_pderiv_diff_primitive :
    ∀ (n : ℕ) (i i' : Fin (n + 1)), i ≠ i' → ∀ (α : Fin (n + 1) →₀ ℕ) (c : ℝ),
      ∃ J₁ R : MvPolynomial (Fin (n + 1)) ℝ, pderiv i' J₁ - pderiv i J₁ = monomial α c ∧
        J₁ = (-(1 / ((α i : ℝ) + 1))) • (X i * monomial α c) + R ∧
        ∀ β ∈ R.support, β i' < α i' ∧ ∀ j, j ≠ i → j ≠ i' → β j = α j :=
  fun n i i' h α c => monomial_pderiv_difference_primitive n i i' h _ α c rfl

end GlobalTheory
