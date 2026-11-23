import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem sum_padicValNat_mul_log_le_log (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h1 : ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p
      = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p :=
    Finset.sum_congr rfl fun p hp => by rw [Nat.factorization_def n (hS p hp)]
  rw [h1]
  have h2 : ∑ p ∈ S ∪ n.factorization.support, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p _ hp => ?_
    rw [Finsupp.notMem_support_iff.1 hp]; simp
  rw [← h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem sum_vDiff_mul_log_le :
    ∀ (D : D7) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ vDiff D p) ∧ ∑ p ∈ S, vDiff D p * Real.log p ≤ Real.log D.host.rdE := by
  intro D S hS
  refine ⟨fun p => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hn : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero D.host.E
  have hc : ((WeightThresholdDefs.dE D : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
    rw [WeightThresholdDefs.dE, Nat.cast_natAbs, Int.cast_abs]
  have hr : Real.log D.host.rdE = Real.log (WeightThresholdDefs.dE D : ℕ) / (Module.finrank ℚ D.host.E : ℝ) := by
    rw [hc]
    unfold Host.rdE
    rw [Real.log_rpow hd]; ring
  rw [hr]
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (sum_padicValNat_mul_log_le_log (WeightThresholdDefs.dE D) S hS) hn.le)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vDiff]; ring

end GlobalTheory.MeanTop
