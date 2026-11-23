import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_pairing_integral_values : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.NormSum.TraceInt.hYY_integral | exact GlobalTheory.NormSum.TraceInt.hYY_integral | (intros; apply GlobalTheory.NormSum.TraceInt.hYY_integral <;> assumption)
