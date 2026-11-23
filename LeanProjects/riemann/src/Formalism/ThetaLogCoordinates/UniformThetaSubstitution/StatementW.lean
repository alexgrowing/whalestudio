import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThmSUniform

noncomputable section

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p →
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧ CompleteSpace K ∧
      ∃ σ : K →+* K, UnrOK K p σ ∧ ∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)

def BetaNonVacuous : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p →
    ∃ (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K)
      (_ : CompleteSpace K) (σ : K →+* K) (F be : MvPowerSeries (Fin 2) K),
      UnrOK K p σ ∧ (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) ∧ IsLawOfLog p F ∧ BetaHyp p F be ∧
        ¬ Simeq be 0

end Formalism.InvariantFactorPaths.G7
