import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteAdeleHaarScalingTotallyReal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_adele_haar_scaling_totally_real : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ n : (Ainf F)ˣ, li.map (fun t => (n : Ainf F) * t) = (∏ w : InfinitePlace F, ‖(n : Ainf F) w‖₊)⁻¹ • li := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarUnit.map_mul_unit | exact GlobalTheory.CompanionTheory.SW.HaarUnit.map_mul_unit | (intros; apply GlobalTheory.CompanionTheory.SW.HaarUnit.map_mul_unit <;> assumption)
