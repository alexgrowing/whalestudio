import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_herm_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.twist_line | exact GlobalTheory.CompanionTheory.Ar.Num.twist_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.twist_line <;> assumption)
