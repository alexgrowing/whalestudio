import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementVectorDecayBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.godement_vector_decay_bound : ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹,
  (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧ Continuous W₀ ∧
  ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B) := by
  first | exact @GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector.godement_vector_growth_support | exact GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector.godement_vector_growth_support | (intros; apply GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector.godement_vector_growth_support <;> assumption)
