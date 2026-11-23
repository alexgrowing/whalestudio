import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTrace
import Mathlib
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_commutes_with_trace : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L] (D : Derivation K L L) (D0 : Derivation K F F), (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) → ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) = algebraMap F L (Algebra.trace F L (D y)) := by
  first | exact @GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | exact GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | (intros; apply GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation <;> assumption)
