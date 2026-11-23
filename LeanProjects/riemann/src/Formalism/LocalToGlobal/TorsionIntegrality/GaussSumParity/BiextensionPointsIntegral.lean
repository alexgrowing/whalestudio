import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)

def TilInvariantL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ u : K, u ^ (l ^ d - 1) = 1 →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms)))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def MeanSimeqL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def BiextensionPointsIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      ∃ Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
        (∀ x, MvPowerSeries.constantCoeff (Xt x) = 0 ∧ Integral (Xt x)) ∧
        (∀ x, PowerSeries.subst (Xt x) (lgF K l) =
          if x.1 = false then
            linEL σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
          else linOL σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) ∧
        Simeq (∑ ab : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s => entLog (K := K) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ))
          (MvPowerSeries.subst Xt (sumE be0))

end Formalism.L2.Th1.D
