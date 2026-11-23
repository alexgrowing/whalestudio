import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  first | exact @GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | exact GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | (intros; apply GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap <;> assumption)
