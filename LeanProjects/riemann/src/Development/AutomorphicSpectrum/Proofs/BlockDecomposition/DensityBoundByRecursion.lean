import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.DensityIter

theorem bounded_density_of_iterated
    (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞)
    (hDtot : Dtot ≠ ⊤) (hD : ∀ Y, MeasurableSet Y → D Y ≤ Dtot)
    (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0)
    (hit : ∀ Y, MeasurableSet Y → ∃ Z : ι → Set H,
      (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧
        D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i))
    (hρ : ∑ i ∈ I, α i * β i < 1) (hr : ∑ i ∈ I, α i < 1) :
    ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  set ρ : ℝ≥0 := ∑ i ∈ I, α i * β i with hρdef
  set r : ℝ≥0 := ∑ i ∈ I, α i with hrdef
  set K : ℝ≥0 := C₀ / (1 - ρ) with hK
  have hKeq : C₀ + K * ρ = K := by
    have h1 : K * (1 - ρ) = C₀ := div_mul_cancel₀ C₀ (tsub_pos_of_lt hρ).ne'
    calc C₀ + K * ρ = K * (1 - ρ) + K * ρ := by rw [h1]
      _ = K * (1 - ρ + ρ) := by rw [mul_add]
      _ = K := by rw [tsub_add_cancel_of_le hρ.le, mul_one]
  have hKeq' : (C₀ : ℝ≥0∞) + K * ρ = K := by exact_mod_cast hKeq
  have hρc : (ρ : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) * β i := by
    simp only [hρdef, ENNReal.coe_finset_sum, ENNReal.coe_mul]
  have hrc : (r : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) := by
    simp only [hrdef, ENNReal.coe_finset_sum]
  have key : ∀ n : ℕ, ∀ Y, MeasurableSet Y → D Y ≤ K * ν Y + (r : ℝ≥0∞) ^ n * Dtot := by
    intro n
    induction n with
    | zero =>
      intro Y hY
      rw [pow_zero, one_mul]
      exact le_add_left (hD Y hY)
    | succ n ih =>
      intro Y hY
      obtain ⟨Z, hZ, hDY⟩ := hit Y hY
      have e1 : ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y)) = K * ρ * ν Y := by
        rw [hρc, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ I, (α i : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n * Dtot) = (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
        rw [← Finset.sum_mul, ← hrc]
        ring
      calc D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i) := hDY
        _ ≤ C₀ * ν Y + ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y) + (r : ℝ≥0∞) ^ n * Dtot) := by
          gcongr with i hi
          rw [← (hZ i hi).2]
          exact ih _ (hZ i hi).1
        _ = C₀ * ν Y + (K * ρ * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot) := by
          simp only [mul_add, Finset.sum_add_distrib, e1, e2]
        _ = K * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
          rw [← add_assoc, ← add_mul, hKeq']
  refine ⟨K, fun Y hY => ?_⟩
  have hr1 : (r : ℝ≥0∞) < 1 := by exact_mod_cast hr
  have ht : Filter.Tendsto (fun n : ℕ => (K : ℝ≥0∞) * ν Y + (r : ℝ≥0∞) ^ n * Dtot) Filter.atTop
      (nhds ((K : ℝ≥0∞) * ν Y + 0 * Dtot)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) (Or.inr hDtot))
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht fun n => key n Y hY

end GlobalTheory.CompanionTheory.DensityIter
