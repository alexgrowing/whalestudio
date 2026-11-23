import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sums_vanish_of_trivial_flags : NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ), (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | exact GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt <;> assumption)
