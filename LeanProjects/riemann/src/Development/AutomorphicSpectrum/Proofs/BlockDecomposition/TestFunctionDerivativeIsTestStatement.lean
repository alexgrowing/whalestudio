import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTest
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_derivative_is_test : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β → ∀ X : Lie E a, IsTest (dTest X β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | exact GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest <;> assumption)
