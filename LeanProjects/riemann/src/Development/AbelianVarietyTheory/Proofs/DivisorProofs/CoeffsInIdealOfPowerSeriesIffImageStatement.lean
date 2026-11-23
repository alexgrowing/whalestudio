import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffsInIdealOfPowerSeries_iff_image : ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q), (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧ ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B, In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  first | exact @GlobalTheory.series_in_ideal_iff_image | exact GlobalTheory.series_in_ideal_iff_image | (intros; apply GlobalTheory.series_in_ideal_iff_image <;> assumption)
