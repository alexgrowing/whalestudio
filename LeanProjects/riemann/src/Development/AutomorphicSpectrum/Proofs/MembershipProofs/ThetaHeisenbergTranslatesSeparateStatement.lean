import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_units_haar_character_one : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (a : Fˣ), distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | exact GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | (intros; apply GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal <;> assumption)
