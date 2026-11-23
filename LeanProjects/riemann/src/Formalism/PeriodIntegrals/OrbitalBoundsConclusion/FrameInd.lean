import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose

theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
