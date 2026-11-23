import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

open NumberField

namespace GlobalTheory.EtaValueBound

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

theorem summable_zeta (M : ℕ) (hM : 2 ≤ M) : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
  simpa using this

theorem zeta_le_two (M : ℕ) (hM : 2 ≤ M) : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ 2 := by
  have h2 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).2 h
    simpa using h'.tsum_eq
  have h3 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
    refine (summable_zeta M hM).tsum_le_tsum (fun m => ?_) (summable_zeta 2 le_rfl)
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hM)
  have h4 := Real.pi_lt_d2
  have h5 := Real.pi_pos
  rw [h2] at h3
  nlinarith

theorem multipliable_pos_abs_log_le (K : Type) [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
      0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log 2 := by
  have hpos : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (euler_factor_log_bound K hK M (by omega) P.1 P.2).1
  have hpart := partial_sums_log_euler_factor_le K hK M hM
  have habs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) hpart
  have hsum : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := habs.of_abs
  have hprod : Real.exp (∑' P : {P : Ideal (𝓞 K) // P.IsMaximal},
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) = Formalism.HermitianLatticesTheory.lValEta K M :=
    Real.rexp_tsum_eq_tprod hpos hsum
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · rw [← hprod]; exact Real.exp_pos _
  · rw [← hprod, Real.log_exp]
    have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
      (summable_zeta M hM).tsum_pos (fun m => by positivity) 0 (by positivity)
    calc |∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun P :
            {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
            (by simpa [Real.norm_eq_abs] using habs)
      _ ≤ _ := habs.tsum_le_of_sum_le hpart
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hz (zeta_le_two M hM)) (Nat.cast_nonneg _)

theorem lValEta_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ _ hK i hi
  obtain ⟨-, h0, h1⟩ := multipliable_pos_abs_log_le K hK i hi
  rw [abs_le] at h1
  have h2 : (0 : ℝ) < 2 ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  constructor
  · rw [← Real.log_le_log_iff (inv_pos.2 h2) h0, Real.log_inv, Real.log_pow]
    exact h1.1
  · rw [← Real.log_le_log_iff h0 h2, Real.log_pow]
    exact h1.2

end GlobalTheory.EtaValueBound
