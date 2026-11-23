import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (n m s : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), S.Ok → (∀ i, b i ∈ S.La) → S.IsTheta e → IsIdem lam S.d m eps → 2 * n ≤ m → (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) → s ≡ 1 [MOD q ^ n] → opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b y) (opU S.Hm t e) ∧ ∀ v ∈ S.La, kap S.Hm v ((s : ℂ) • liftY q n eps b y) = kap S.Hm v (liftY q n eps b y) := by
  first | exact @GlobalTheory.MomOne.lift_change | exact GlobalTheory.MomOne.lift_change | (intros; apply GlobalTheory.MomOne.lift_change <;> assumption)
