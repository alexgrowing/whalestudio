import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVectorGaugeBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vector_gauge_bound : ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', Continuous W ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : GL (Fin 2) F,
  ‖W h‖ ≤ C * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε) := by
  first | exact @GlobalTheory.CompanionTheory.WhIwasawa.continuous_and_iwasawa_bound | exact GlobalTheory.CompanionTheory.WhIwasawa.continuous_and_iwasawa_bound | (intros; apply GlobalTheory.CompanionTheory.WhIwasawa.continuous_and_iwasawa_bound <;> assumption)
