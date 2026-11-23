import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinors
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringOHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zEquiv_gram_bounded_minors : ∀ (K : Type) [Field K] [NumberField K], (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (p : Point K (r + 1)), IsInCell (ZhatOM Z) p → ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZEquiv Z Z₂ ∧ ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) * ∏ l ∈ Finset.Icc 1 (r + 1), (max 1 ‖τ (leadMinorE Z l)‖ * max 1 ‖τ (leadMinorE Z l)‖⁻¹) := by
  first | exact @GlobalTheory.ReducedGram.exists_reduced | exact GlobalTheory.ReducedGram.exists_reduced | (intros; apply GlobalTheory.ReducedGram.exists_reduced <;> assumption)
