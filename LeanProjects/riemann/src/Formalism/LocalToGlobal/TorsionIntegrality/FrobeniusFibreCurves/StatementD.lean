import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def WronskLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A Bs : MvPowerSeries (Fin 3) K),
    A * pd 2 Bs = Bs * pd 2 A → ev3 A = ev3 Bs → ev3 Bs ≠ 0 → A = Bs

def ShearLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A Bs : MvPowerSeries (Fin 3) K),
    A * (pd 1 Bs - pd 2 Bs) = Bs * (pd 1 A - pd 2 A) → ev3 A = ev3 Bs → ev3 Bs ≠ 0 → A = Bs

def TauRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (pd 0 (wpDiff P) - pd 1 (wpDiff P)) =
      wpDiff P * (2 + 2 * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
        (atD (dz (sigS P)) - at1 0 (dz (sigS P)) + at1 1 (dz (sigS P))))

def DetRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    2 * wp3 P 0 1 * wp3 P 0 2 * wp3 P 1 2 * (pd 1 (det3 P) - pd 2 (det3 P)) =
      det3 P *
        (-(pd 0 (wp3 P 0 1) - pd 1 (wp3 P 0 1)) * wp3 P 0 2 * wp3 P 1 2 +
          (pd 0 (wp3 P 0 2) - pd 2 (wp3 P 0 2)) * wp3 P 0 1 * wp3 P 1 2 +
          2 * (pd 1 (wp3 P 1 2) - pd 2 (wp3 P 1 2)) * wp3 P 0 1 * wp3 P 0 2)

def FrobStickLog : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    det3 P = -2 * vand3 K * fExp (fsE (sigS P))

def FrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (at1 0 (sigma P) * at1 1 (sigma P) * at1 2 (sigma P)) ^ 3 * det3 P =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sigma P) * evalDiffThree 0 1 (sigma P) * evalDiffThree 0 2 (sigma P) * evalDiffThree 1 2 (sigma P))

def FrobStickStar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (at1 0 (sgStar s2 P) * at1 1 (sgStar s2 P) * at1 2 (sgStar s2 P)) ^ 3 * det3 P =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgStar s2 P) * evalDiffThree 0 1 (sgStar s2 P) * evalDiffThree 0 2 (sgStar s2 P) *
          evalDiffThree 1 2 (sgStar s2 P))

def FIUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i : PowerSeries K), LawLog F l → IsInv l i →
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n

def ParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    Simeq (par3 F i (phO s2 P l)) 0

def CubeFromPars : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i →
    Simeq (par F i f) 0 → Simeq (par3 F i f) 0 → Simeq (d1 F (cob F f)) 0

def LogSigmaPullbackCocycleJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    DivAB (cob F (phO s2 P l)) ∧ swap2 (cob F (phO s2 P l)) = cob F (phO s2 P l) ∧
      Simeq (d1 F (cob F (phO s2 P l))) 0 ∧ Simeq (d1 F (swap2 (cob F (phO s2 P l)))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] (phO s2 P l))‖ ≤ 1

end Formalism.L2.Th1.B
