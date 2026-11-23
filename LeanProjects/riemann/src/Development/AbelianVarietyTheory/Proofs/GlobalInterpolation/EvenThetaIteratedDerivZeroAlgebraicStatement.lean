import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaIteratedDerivZeroAlgebraic
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_th0_zero_mem_Qbar : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ Qbar := by
  first | exact @GlobalTheory.ThetaZeroAlg.evenTheta_iteratedDeriv_zero_algebraic | exact GlobalTheory.ThetaZeroAlg.evenTheta_iteratedDeriv_zero_algebraic | (intros; apply GlobalTheory.ThetaZeroAlg.evenTheta_iteratedDeriv_zero_algebraic <;> assumption)
