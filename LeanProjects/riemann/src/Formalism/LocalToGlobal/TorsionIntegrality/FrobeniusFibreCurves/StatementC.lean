import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def PhESimPhO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → 4 * e1 ^ 3 - g2 * e1 - g3 = 0 → LawLog F l → CurveHyp F i l P ep c0 →
    ‖c0 - e1‖ ≤ 1 → ‖(2 : K)‖ = 1 →
    Simeq (ι := Unit) (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l) (phO s2 P l)

def SigmaOneCocycleShifted : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → 4 * e1 ^ 3 - g2 * e1 - g3 = 0 → LawLog F l → IsInv l i →
    CurveHyp F i l P ep c0 → ‖c0 - e1‖ ≤ 1 → ‖3 * e1 ^ 2 - g2 / 4‖ ≤ 1 → ‖(2 : K)‖ = 1 →
    DivAB (cob F (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l)) ∧
      Simeq (d1 F (cob F (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l))) 0 ∧
      Simeq (d1 F (swap2 (cob F (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l)))) 0

def JetOne : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i f : PowerSeries K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 → IsInv l i →
    Simeq (ι := Unit) (PowerSeries.subst i f) f →
    ‖2 * PowerSeries.constantCoeff (Dinv l f)‖ ≤ 1

def JetsPhO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → ‖(2 : K)‖ = 1 →
    ∀ n : ℕ, n = 1 ∨ 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] (phO s2 P l))‖ ≤ 1

def MulExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ∀ n : ℤ, ∃ N : PowerSeries K,
      PowerSeries.constantCoeff N = 0 ∧ Integral (ι := Unit) N ∧
        PowerSeries.subst N l = PowerSeries.C (n : K) * l

def MulSq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → Simeq (par F i f) 0 →
    ∀ (n : ℤ) (N : PowerSeries K), PowerSeries.constantCoeff N = 0 →
      PowerSeries.subst N l = PowerSeries.C (n : K) * l →
      Simeq (ι := Unit) (PowerSeries.subst N f) (((n ^ 2 : ℤ) : PowerSeries K) * f)

def AddMul : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → Simeq (cob F f) 0 →
    ∀ (n : ℤ) (N : PowerSeries K), PowerSeries.constantCoeff N = 0 →
      PowerSeries.subst N l = PowerSeries.C (n : K) * l →
      Simeq (ι := Unit) (PowerSeries.subst N f) ((n : PowerSeries K) * f)

def BiaddMul : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F be : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → Simeq (d1 F be) 0 →
    ∀ (n : ℤ) (N : PowerSeries K), PowerSeries.constantCoeff N = 0 →
      PowerSeries.subst N l = PowerSeries.C (n : K) * l →
      Simeq (MvPowerSeries.subst ![at1 0 N, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be)
        ((n : MvPowerSeries (Fin 2) K) * be)

def BaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
    (s2 e1 kap : K) (P w l : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    MvPowerSeries.constantCoeff F = 0 →
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) ∧
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) ∧
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) ∧
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) ∧
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) ∧
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) ∧
    ∀ f : PowerSeries K, MvPowerSeries.map j (cob F f) =
      cob (MvPowerSeries.map j F) (PowerSeries.map j f)

end Formalism.L2.Th1.B
