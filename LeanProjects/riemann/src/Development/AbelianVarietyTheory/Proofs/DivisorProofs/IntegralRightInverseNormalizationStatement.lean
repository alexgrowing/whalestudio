import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_inverse_normalization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ) (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k), Y * Q' = 1 → ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k), (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  first | exact @GlobalTheory.frame_normalise_integral | exact GlobalTheory.frame_normalise_integral | (intros; apply GlobalTheory.frame_normalise_integral <;> assumption)
