import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_lie_preserves_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) → ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | exact GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | (intros; apply GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable <;> assumption)
