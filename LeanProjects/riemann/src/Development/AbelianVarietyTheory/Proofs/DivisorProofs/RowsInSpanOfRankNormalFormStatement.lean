import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_in_span_of_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K) (Q : Matrix D (Fin r) K), X.rank ≤ r → IsUnit (H * X * Q) → ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  first | exact @GlobalTheory.rows_mem_span_of_isUnit_mul | exact GlobalTheory.rows_mem_span_of_isUnit_mul | (intros; apply GlobalTheory.rows_mem_span_of_isUnit_mul <;> assumption)
