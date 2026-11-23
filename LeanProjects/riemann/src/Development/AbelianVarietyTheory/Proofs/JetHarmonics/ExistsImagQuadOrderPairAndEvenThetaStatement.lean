import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenTheta
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  first | exact @GlobalTheory.MomOne.exists_pair_and_isTh | exact GlobalTheory.MomOne.exists_pair_and_isTh | (intros; apply GlobalTheory.MomOne.exists_pair_and_isTh <;> assumption)
