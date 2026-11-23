import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPos
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → 0 < m → (m : ℂ)⁻¹ ∈ W → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧ ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  first | exact @GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos | exact GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos | (intros; apply GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos <;> assumption)
