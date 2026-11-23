import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVanishOnFiberTangent
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vanish_on_fiber_tangent : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ ξ, fderiv ℂ π y ξ = 0 → (∀ i l, i < l → thetaOneZero H π e y ξ l i = 0) →
      FixesFlag A y ξ := by
  first | exact @GlobalTheory.VertFlag.vertical_fixesFlag | exact GlobalTheory.VertFlag.vertical_fixesFlag | (intros; apply GlobalTheory.VertFlag.vertical_fixesFlag <;> assumption)
