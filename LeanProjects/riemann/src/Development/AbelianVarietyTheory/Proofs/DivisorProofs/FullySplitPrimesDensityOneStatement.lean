import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullySplitPrimesDensityOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TrivialOfDensityOne
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fully_split_primes_density_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsGalois ℚ E → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), NumberField.Set.HasDirichletDensity {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∉ T ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E (w.under (𝓞 F))} 1 := by
  first | exact @GlobalTheory.DensitySplit.hasDirichletDensity_splitsFully | exact GlobalTheory.DensitySplit.hasDirichletDensity_splitsFully | (intros; apply GlobalTheory.DensitySplit.hasDirichletDensity_splitsFully <;> assumption)
