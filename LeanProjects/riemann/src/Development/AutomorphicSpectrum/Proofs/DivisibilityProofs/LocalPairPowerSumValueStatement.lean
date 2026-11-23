import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairPowerSumValue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_pair_power_sum_value : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] [DecidableEq σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (r k : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) = ∑ μ ∈ G.support, G.coeff μ * (((T.comp e).ck P k (classList (Sum.elim T.x T.x') μ) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul | exact GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul <;> assumption)
