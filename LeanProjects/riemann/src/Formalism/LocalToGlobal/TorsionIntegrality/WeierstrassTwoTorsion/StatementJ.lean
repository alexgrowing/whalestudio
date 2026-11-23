import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.B.IsWp (g₂ W) (g₃ W) (wpReg W)

def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.LawLog (fgl W) (logSer W) ∧ Formalism.L2.Th1.B.IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → Formalism.L2.Th1.B.IsHalf (logSer W) (halfSer W))

def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)

def BridgeTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (xT yT : K), W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    (tS W xT).subst (expSer W) = Formalism.L2.Th1.B.wOf (xT + W.b₂ / 12) (wpReg W) ∧
    Formalism.L2.Th1.B.IsW (3 * (xT + W.b₂ / 12)) (3 * (xT + W.b₂ / 12) ^ 2 - g₂ W / 4)
      ((tS W xT).subst (expSer W)) ∧
    (IntModel W → ‖xT‖ ≤ 1 → Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) (tS W xT))

end Formalism.L2.Th1.A
