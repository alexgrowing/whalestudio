import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtAdeleMulOfPlaceComponentEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q → ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 → ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  first | exact @GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | exact GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero <;> assumption)
