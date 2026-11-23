import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivSubOneLeThreeMulLogAddOne
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadCount

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem sum_setB_log_div_le {D : D7} (Y : ShimX D.what₂.Tau) (hF : FewBad Y) (B : ℝ) (hB : 48 ≤ B) :
    (∀ p ∈ setB Y B, p.Prime) ∧
      ∑ p ∈ setB Y B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B + Real.log D.host.rdE / 12 := by
  have hp : ∀ p ∈ setB Y B, p.Prime := by
    intro p hp
    simp only [setB, Finset.mem_union, Finset.mem_filter] at hp
    rcases hp with h | h | h
    · exact h.2
    · exact Nat.prime_of_mem_primeFactors h
    · exact Y.lev_prime p h
  refine ⟨hp, ?_⟩
  have hfl : 48 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB)
  have h := D.host.sum_log_div_le_of_bad ⌊B⌋₊ Y.lev (setB Y B) (by omega) (by unfold FewBad at hF; omega) hp
    fun p h1 h2 => by
      rw [setB, Finset.mem_union] at h1
      rcases h1 with h | h
      · rw [Finset.mem_filter, Finset.mem_range] at h
        omega
      · exact h
  have h0 := D.host.log_rdE_nonneg'
  have h48 : 4 * Real.log D.host.rdE / (⌊B⌋₊ : ℝ) ≤ 4 * Real.log D.host.rdE / 48 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by exact_mod_cast hfl)
  have hl : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊B⌋₊)) (Nat.floor_le (by linarith))
  have h1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  linarith

end GlobalTheory.Mean4
