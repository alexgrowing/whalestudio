import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementQ
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

def WpPrimeInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 3 * (-2 + logSer W ^ 3 * (derivative K (wpReg W)).subst (logSer W)) =
      logSer W ^ 3 * (-2 * xS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)

def BridgeCurve3 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp3 (fgl W) (logSer W) (wpReg W) (xS W) W.a₁ W.a₃

end Formalism.L2.Th1.A
