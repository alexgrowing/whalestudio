import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_fixed_subspace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective | exact GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective <;> assumption)
