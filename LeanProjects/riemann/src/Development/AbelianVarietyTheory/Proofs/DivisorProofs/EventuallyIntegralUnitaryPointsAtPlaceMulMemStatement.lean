import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (exact GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (intros; apply GlobalTheory.OrbFinAf.mul_mem_IntV_eventually  <;> assumption)
