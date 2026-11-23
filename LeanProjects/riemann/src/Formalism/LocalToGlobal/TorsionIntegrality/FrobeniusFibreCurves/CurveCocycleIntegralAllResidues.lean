import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)

def CurveFrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    (at1 0 (sgW W s2) * at1 1 (sgW W s2) * at1 2 (sgW W s2)) ^ 3 * det3 (wpReg W) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgW W s2) * evalDiffThree 0 1 (sgW W s2) * evalDiffThree 0 2 (sgW W s2) * evalDiffThree 1 2 (sgW W s2))

def CurveParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → Simeq (par3 (fgl W) (iSer W) (phW W s2)) 0

def CurveCocycleIntegralAllResidues : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv (logSer W))^[n] (phW W s2))‖ ≤ 1

end Formalism.L2.Th1.B
