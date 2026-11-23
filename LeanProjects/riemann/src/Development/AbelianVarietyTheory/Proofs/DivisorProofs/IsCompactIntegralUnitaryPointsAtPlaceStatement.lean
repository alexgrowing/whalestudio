import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_IntV) | (exact GlobalTheory.OrbFinAf.isCompact_IntV) | (intros; apply GlobalTheory.OrbFinAf.isCompact_IntV  <;> assumption)
