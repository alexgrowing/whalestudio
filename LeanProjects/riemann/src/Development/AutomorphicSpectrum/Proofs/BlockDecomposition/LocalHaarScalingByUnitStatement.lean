import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnit
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_scaling_by_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), lam.IsAddHaarMeasure → ∀ n : (Fv F v)ˣ, lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  first | exact @GlobalTheory.CompanionTheory.Haar.map_mul_left | exact GlobalTheory.CompanionTheory.Haar.map_mul_left | (intros; apply GlobalTheory.CompanionTheory.Haar.map_mul_left <;> assumption)
