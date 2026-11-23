import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

abbrev Ex (D : ℕ) : P D ≃ₐ[ℤ] MvPolynomial (Fin D) (MvPolynomial (Fin D) ℤ) := sumAlgEquiv ℤ (Fin D) (Fin D)

def cmp {D : ℕ} (β : Fin D →₀ ℕ) (f : P D) : P D := rename Sum.inr (coeff β (Ex D f))

lemma Ex_inl {D : ℕ} (s : S D) :
    Ex D (rename Sum.inl s) = map (C : ℤ →+* MvPolynomial (Fin D) ℤ) s := by
  induction s using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma Ex_inr {D : ℕ} (g : S D) : Ex D (rename Sum.inr g) = C g := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma cmp_zero {D : ℕ} (β : Fin D →₀ ℕ) : cmp β (0 : P D) = 0 := by simp [cmp]

lemma sum_cmp {D : ℕ} (f : P D) (B : Finset (Fin D →₀ ℕ)) (hB : (Ex D f).support ⊆ B) :
    ∑ β ∈ B, inx (monomial β 1) * cmp β f = f := by
  apply (Ex D).injective
  rw [map_sum]
  have h : ∀ β ∈ B, Ex D (inx (monomial β 1) * cmp β f) = monomial β (coeff β (Ex D f)) := by
    intro β _
    rw [map_mul, inx, cmp, Ex_inl, Ex_inr, map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.sum_congr rfl h]
  conv_rhs => rw [as_sum (Ex D f)]
  symm
  refine Finset.sum_subset hB fun β _ hβ => ?_
  rw [mem_support_iff, not_not] at hβ
  simp [hβ]

end PI.EagonNorthcottZ
