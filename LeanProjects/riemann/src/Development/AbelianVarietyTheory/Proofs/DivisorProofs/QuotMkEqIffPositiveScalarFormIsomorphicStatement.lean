import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G), Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  first | (exact @GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (exact GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (intros; apply GlobalTheory.LKCx.Form.mk_eq_iff_rel <;> assumption)
