import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_continuous_compact_support : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | exact GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst <;> assumption)
