import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelevantPrimeOverMultihomog
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevant_prime_over_multihomog : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → z ∈ ReciprocityTheory.ChartRestriction.G.Geo.mcPts P → ∃ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime ∧ P ≤ W ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W ∧ (∀ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) ∧ ∀ s : MvPolynomial (Σ k, ι k) ℤ, s ∉ W → ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ) (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a s)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime | exact GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime <;> assumption)
