import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBaseChangeSq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_module_base_change_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ, (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF | exact GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF | (intros; apply GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF <;> assumption)
