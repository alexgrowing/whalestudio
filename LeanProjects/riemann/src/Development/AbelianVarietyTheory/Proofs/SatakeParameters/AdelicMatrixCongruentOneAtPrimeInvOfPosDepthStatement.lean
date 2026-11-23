import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeInvOfPosDepth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixCongruentOneAtPrime_inv_of_pos_depth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), 1 ≤ n → GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k⁻¹ := by
  first | exact @GlobalTheory.TwU.congAt_inv_pos_depth | exact GlobalTheory.TwU.congAt_inv_pos_depth | (intros; apply GlobalTheory.TwU.congAt_inv_pos_depth <;> assumption)
