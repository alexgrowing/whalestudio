import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransform
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_range_complement_transform : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det → Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft <;> assumption)
