import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaZeroOneSkewConj
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_zero_one_skew_conj : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ k l η, thetaZeroOne e y η k l = -conj (thetaOneZero H π e y η l k) := by
  first | exact @GlobalTheory.HermFrame.thetaZeroOne_eq_neg_conj_thetaOneZero | exact GlobalTheory.HermFrame.thetaZeroOne_eq_neg_conj_thetaOneZero | (intros; apply GlobalTheory.HermFrame.thetaZeroOne_eq_neg_conj_thetaOneZero <;> assumption)
