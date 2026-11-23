import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ), Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) → Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) → Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  first | (exact @GlobalTheory.TenFin.finite_intKQ_quot) | (exact GlobalTheory.TenFin.finite_intKQ_quot) | (intros; apply GlobalTheory.TenFin.finite_intKQ_quot  <;> assumption)
