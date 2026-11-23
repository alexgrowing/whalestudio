import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRealEmbeddingsEqTraceTotallyReal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : F), ∑ i : Emb F, ((i y : ℝ) : ℂ) = ((Algebra.trace ℚ F y : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.sum_realEmb_eq_trace | exact GlobalTheory.HilbFam.sum_realEmb_eq_trace | (intros; apply GlobalTheory.HilbFam.sum_realEmb_eq_trace <;> assumption)
