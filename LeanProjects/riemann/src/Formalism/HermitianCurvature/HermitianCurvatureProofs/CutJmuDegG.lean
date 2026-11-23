import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeBoundOfHolomorphicContinuation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def NormDegG [CompleteSpace Wp] [CompleteSpace Wq] (p : KB.Pl P Wp Wq) : Prop :=
  ∀ (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ),
    F.Good p.T.base lam0 q0 → NormDeg p F lam0 q0

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
