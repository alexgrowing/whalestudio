import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LiftMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Taylor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem steps_of (hBQ : BallQuot) : Steps := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  have h3 := unit_columns_holds G la Q S CRm T c hOk hw
  exact ⟨image_filtration_decreasing G la T,
    pole_length_assemble G la Q S CRm T e c hOk hw hL (hasse_preserves_kernel G la) (vanishingOnQuadric G la) h3 (taylor_holds G la)
      (column_derivative G la) (restricted_derivative_linear G la) (liftMul_of Q T hOk.2.1 h3),
    ball_product_length piLen_holds hBQ G la Q S CRm T e c hOk⟩

theorem pole_length_bound_of_balls (hBQ : BallQuot) : PI.LengthPoleInLift := target filtration_length_bound sum_antidiagonalTuple (steps_of hBQ)

end PI.PoleLengthCount
