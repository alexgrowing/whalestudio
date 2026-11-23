import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powers_linearIndependent_over_localTensorCenter : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F), ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  first | (exact @GlobalTheory.OrbFinAf.pow_indep_tensor) | (exact GlobalTheory.OrbFinAf.pow_indep_tensor) | (intros; apply GlobalTheory.OrbFinAf.pow_indep_tensor  <;> assumption)
