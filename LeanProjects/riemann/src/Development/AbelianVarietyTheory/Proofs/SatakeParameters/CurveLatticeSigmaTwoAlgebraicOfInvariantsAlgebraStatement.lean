import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  first | exact @GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | exact GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | (intros; apply GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg <;> assumption)
