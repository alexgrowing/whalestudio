import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingLocalizationPowerSeriesUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime, IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  first | exact @GlobalTheory.PowerSeriesUniformiser.main | exact GlobalTheory.PowerSeriesUniformiser.main | (intros; apply GlobalTheory.PowerSeriesUniformiser.main <;> assumption)
