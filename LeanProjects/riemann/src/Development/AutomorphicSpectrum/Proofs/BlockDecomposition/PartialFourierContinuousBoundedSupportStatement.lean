import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierContinuousBoundedSupport
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_continuous_bounded_support : ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F, Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) ∧
  ∃ C R : ℝ, 0 ≤ C ∧ ∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C ∧
    (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R) := by
  first | exact @GlobalTheory.CompanionTheory.PFTBound.pFT_continuous_bounded | exact GlobalTheory.CompanionTheory.PFTBound.pFT_continuous_bounded | (intros; apply GlobalTheory.CompanionTheory.PFTBound.pFT_continuous_bounded <;> assumption)
