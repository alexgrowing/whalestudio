import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantAlgebraComparison.BridgeHomFormula

noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem matEq_of_inj (hi : ThetaInj) (I : AutInst)
    {A B : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)}
    (hv : ∀ v, A.map (thetaV I v) = B.map (thetaV I v)) (hf : A.map (tauF I) = B.map (tauF I)) :
    A = B := by
  ext i j
  apply hi I
  rw [theta_apply, theta_apply]
  refine Prod.ext (funext fun v => ?_) ?_
  · exact congrArg (fun M => M i j) (hv v)
  · exact congrArg (fun M => M i j) hf

end PI.UnitaryGroupMassFormula.BridgeInvAlg
