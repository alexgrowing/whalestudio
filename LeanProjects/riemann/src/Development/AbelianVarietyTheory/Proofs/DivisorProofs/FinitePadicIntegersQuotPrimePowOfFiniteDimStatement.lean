import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (m : ℕ), Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  first | (exact @GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (exact GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (intros; apply GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow  <;> assumption)
