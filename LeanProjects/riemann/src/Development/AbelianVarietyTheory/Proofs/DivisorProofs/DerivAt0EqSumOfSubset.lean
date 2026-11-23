import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem derivAt0_eq_sum_of_subset {C : Type} [Field C] {σ : Type} (P : MvPolynomial σ C)
    (g : MvPowerSeries σ C) {s : Finset (σ →₀ ℕ)} (hs : P.support ⊆ s) :
    derivAt0 P g = ∑ α ∈ s, P.coeff α * mfact α * coeff α g := by
  unfold derivAt0
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.mp hα]
  simp

theorem derivAt0_linear (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (σ : Type) (P Q : MvPolynomial σ C) (g g' : MvPowerSeries σ C) (a : C) :
    derivAt0 P (g + g') = derivAt0 P g + derivAt0 P g' ∧
      derivAt0 P (a • g) = a * derivAt0 P g ∧
      derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g ∧
      derivAt0 (a • P) g = a * derivAt0 P g ∧
      ((∀ α ∈ P.support, coeff α g = coeff α g') → derivAt0 P g = derivAt0 P g') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold derivAt0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_add, mul_add]
  · unfold derivAt0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  · classical
    rw [derivAt0_eq_sum_of_subset (P + Q) g (MvPolynomial.support_add (p := P) (q := Q)),
      derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
      derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_add]
    ring
  · rw [derivAt0_eq_sum_of_subset (a • P) g (MvPolynomial.support_smul (a := a) (f := P)),
      derivAt0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  · intro h
    unfold derivAt0
    exact Finset.sum_congr rfl fun α hα => by rw [h α hα]

end GlobalTheory.FGDepth
