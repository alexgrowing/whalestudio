import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries : ∀ (σ R : Type) [CommRing R] (D : Derivation ℤ R R), ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R), ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  first | exact @GlobalTheory.mvPowerSeries_derivation_coeffwise | exact GlobalTheory.mvPowerSeries_derivation_coeffwise | (intros; apply GlobalTheory.mvPowerSeries_derivation_coeffwise <;> assumption)
