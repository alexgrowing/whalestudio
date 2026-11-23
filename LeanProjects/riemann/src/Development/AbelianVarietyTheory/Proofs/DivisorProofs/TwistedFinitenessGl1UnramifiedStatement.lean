import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessGl1Unramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_gl1_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r), GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  first | (exact @GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (exact GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (intros; apply GlobalTheory.TwFinGL1.twisted_finiteness_gl1  <;> assumption)
