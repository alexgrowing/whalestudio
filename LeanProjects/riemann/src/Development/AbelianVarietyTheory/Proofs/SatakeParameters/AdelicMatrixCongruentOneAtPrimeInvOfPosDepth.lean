import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
open NumberField IsDedekindDomain

theorem GlobalTheory.TwU.congAt_inv_pos_depth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))),
    1 ≤ n → GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k⁻¹ :=
  fun F E _ _ _ _ _ Q n N k hn hk => GlobalTheory.LevFrame.congAt_inv F E N n Q k hn hk
