import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirections
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  first | exact @GlobalTheory.CuspRapid.lieD_le_of_basis | exact GlobalTheory.CuspRapid.lieD_le_of_basis | (intros; apply GlobalTheory.CuspRapid.lieD_le_of_basis <;> assumption)
