import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [CompleteSpace Wp] [CompleteSpace Wq]
variable {Bs : B.RealPlaceData k r Wp Wq} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
  {u u' : Fin k → ℝ} {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} {A : JDat k r Wp Wq}

theorem lowest_unit_vector_is_K_finite (hG : A.Good Bs ε lam h u u' νq νq') : PI.UpqRep.IsKFinHpk (k := k) (r := r) A.σ A.w0 :=
  PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hG.1.2.2.2.2.1

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
