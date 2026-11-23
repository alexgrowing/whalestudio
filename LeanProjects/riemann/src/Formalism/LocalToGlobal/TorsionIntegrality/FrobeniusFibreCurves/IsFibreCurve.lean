import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.DivByXSq
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr)

section Alg

variable {K : Type} [Field K] [CharZero K]

abbrev phTw (g2 s2 c0 xT : K) (P l : PowerSeries K) : PowerSeries K :=
  phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l

abbrev thTw (g2 s2 c0 xT : K) (P : PowerSeries K) : PowerSeries K :=
  thZ s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P)

def IsFibreZ (P tr : PowerSeries K) {ι : Type} [Fintype ι] (c : ι → K)
    (wp wm : ι → PowerSeries K) (al S : K) : Prop :=
  (∀ Q, HasSecondLogDeriv (wpShift P (c Q)) (2 * P - wp Q - wm Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al tr = ∑ Q, (wp Q + wm Q) - PowerSeries.C S

def IsFibreCurve (W : WeierstrassCurve K) (xT yT : K) {ι : Type} [Fintype ι] (xQ yQ : ι → K)
    (al S : K) : Prop :=
  (∀ Q, W.toAffine.Equation (xQ Q) (yQ Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wTr W xT yT) =
      ∑ Q, (wTr W (xQ Q) (yQ Q) + wTr W (xQ Q) (W.toAffine.negY (xQ Q) (yQ Q))) - PowerSeries.C S

end Alg

end Formalism.L2.Th1.B
