import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Crv2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS tS xPlus bridgeWp bridgeLaw
  bridgeCurve bridgeCurve3)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) :=
  (Formalism.L2.Th1.C.curveFrame K ⊤ W ⟨trivial, trivial, trivial, trivial, trivial⟩).1

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem twoHyp (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (hE : W.toAffine.Equation xT yT) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1)
    (hy : ‖yT‖ ≤ 1) : TwoHyp (g₂ W) (g₃ W) (W.b₂ / 12) W.a₁ W.a₃ xT yT :=
  ⟨h2, Crv.two_torsion_x_root_of_cubic W xT yT hE h2, hx, hy, hW.1, Crv.norm_kap W xT yT hW h2 hx hy⟩

end Norm

end Formalism.L2.Th1.B.Crv2
