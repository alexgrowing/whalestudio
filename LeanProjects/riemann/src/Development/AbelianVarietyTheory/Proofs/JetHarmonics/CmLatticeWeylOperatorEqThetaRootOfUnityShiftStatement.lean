import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeWeylOperatorEqThetaRootOfUnityShift
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → hat M.ι (C ω * logS) (W1 d y θ) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) θ) := by
  first | exact @GlobalTheory.MomOne.ThShift.theta_shift | exact GlobalTheory.MomOne.ThShift.theta_shift | (intros; apply GlobalTheory.MomOne.ThShift.theta_shift <;> assumption)
