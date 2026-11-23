import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaZeroOneLowerVanish
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_zero_one_lower_vanish : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ k l η, k < l → thetaZeroOne e y η l k = 0 := by
  first | exact @GlobalTheory.Proof.theta_zero_one_lower_vanish.thetaZeroOne_lower_eq_zero | exact GlobalTheory.Proof.theta_zero_one_lower_vanish.thetaZeroOne_lower_eq_zero | (intros; apply GlobalTheory.Proof.theta_zero_one_lower_vanish.thetaZeroOne_lower_eq_zero <;> assumption)
