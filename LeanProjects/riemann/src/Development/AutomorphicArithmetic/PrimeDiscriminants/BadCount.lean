import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivSubOneLeThreeMulLogAddOne

open NumberField

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem log_rdE_nonneg' : 0 ≤ Real.log H.rdE := by
  have h := H.log_n_le_two_log_rdE
  have := Real.log_natCast_nonneg R.n
  linarith

theorem sum_small_gt_log_div_le {B : ℕ} (hB : 1 ≤ B) (T : Finset ℕ) (hT : ∀ p ∈ T, p ∈ H.small ∧ B < p) :
    ∑ p ∈ T, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log H.rdE / B := by
  have hB0 : (0:ℝ) < B := by exact_mod_cast hB
  calc ∑ p ∈ T, Real.log p / ((p : ℝ) - 1) ≤ ∑ p ∈ T, Real.log p / (B:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hBp : B < p := (hT p hp).2
        have hBp' : (B:ℝ) ≤ (p:ℝ) - 1 := by
          have : ((B + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hBp
          push_cast at this
          linarith
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hB0 hBp'
    _ = (∑ p ∈ T, Real.log (p:ℝ)) / B := (Finset.sum_div _ _ _).symm
    _ ≤ (∑ p ∈ H.small, Real.log (p:ℝ)) / B := by
        apply div_le_div_of_nonneg_right _ hB0.le
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (hT p hp).1)
          (fun p _ _ => Real.log_natCast_nonneg p)
    _ ≤ 4 * Real.log H.rdE / B := div_le_div_of_nonneg_right (sum_small_log_le H) hB0.le

theorem sum_bad_log_div_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S, Real.log p / ((p : ℝ) - 1) ≤
      S.card + 2 + 4 * Real.log H.rdE := by
  set U := Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S with hU
  have hprime : ∀ p ∈ U, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact hS p h
  have hterm1 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ 1 := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    rw [div_le_one (by linarith)]
    exact Real.log_le_sub_one_of_pos (by linarith)
  have hterm2 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ Real.log p := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact div_le_self (Real.log_natCast_nonneg p) (by linarith)
  rw [← Finset.sum_filter_add_sum_filter_not U (· ∈ H.small)]
  have hA : ∑ p ∈ U.filter (· ∈ H.small), Real.log p / ((p:ℝ) - 1) ≤ 4 * Real.log H.rdE := by
    calc _ ≤ ∑ p ∈ U.filter (· ∈ H.small), Real.log (p:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm2 p (Finset.mem_filter.mp hp).1
      _ ≤ ∑ p ∈ H.small, Real.log (p:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
            (fun p _ _ => Real.log_natCast_nonneg p)
      _ ≤ _ := sum_small_log_le H
  have hB : ∑ p ∈ U.filter (· ∉ H.small), Real.log p / ((p:ℝ) - 1) ≤ S.card + 2 := by
    calc _ ≤ ∑ p ∈ U.filter (· ∉ H.small), (1:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm1 p (Finset.mem_filter.mp hp).1
      _ = ((U \ H.small).card : ℝ) := by rw [Finset.sum_const, nsmul_one, Finset.sdiff_eq_filter]
      _ ≤ _ := by exact_mod_cast card_bad_sdiff_le H S
  linarith

theorem sum_log_div_le_of_bad (B : ℕ) (S T : Finset ℕ) (hB : 3 ≤ B) (hS : S.card + 2 ≤ B) (hp : ∀ p ∈ T, p.Prime)
    (hT : ∀ p ∈ T, B < p → p ∈ Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) :
    ∑ p ∈ T, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 + 4 * Real.log H.rdE / B := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun p => p ∈ H.small ∧ B < p)]
  have h1 := H.sum_small_gt_log_div_le (B := B) (by omega) (T.filter fun p => p ∈ H.small ∧ B < p)
    fun p h => (Finset.mem_filter.1 h).2
  have h2 := GlobalTheory.sum_log_div_sub_one_le_three_mul_log_add_one B (T.filter fun p => ¬ (p ∈ H.small ∧ B < p)) hB
    (fun p h => hp p (Finset.mem_filter.1 h).1) (by
      refine ((Finset.card_le_card fun p h => ?_).trans (H.card_bad_sdiff_le S)).trans hS
      obtain ⟨h, hb⟩ := Finset.mem_filter.1 h
      obtain ⟨h, hn⟩ := Finset.mem_filter.1 h
      exact Finset.mem_sdiff.2 ⟨hT p h hb, fun hs => hn ⟨hs, hb⟩⟩)
  linarith

end Formalism.BasicNotions.Host
