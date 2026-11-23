import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumMixedExpansion
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sum_mixed_expansion : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | exact GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul <;> assumption)
