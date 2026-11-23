import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelGenericSpecialDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_model_generic_special_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ η : B.X, IsGenSpecial B η → IsDiscreteValuationRing (B.X.presheaf.stalk η) := by
  first | exact @GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk | exact GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk | (intros; apply GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk <;> assumption)
