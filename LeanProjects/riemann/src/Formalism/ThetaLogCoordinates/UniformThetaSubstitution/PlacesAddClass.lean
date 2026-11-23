import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementM

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)

def PlacesAddClass : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype Pl] [DecidableEq Pl]
    (ι : Pl → Type) [∀ v, Fintype (ι v)] (p : ℕ) (ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ (P : ∀ v, MvPolynomial (ι v) K) (hh : ∀ v, MvPowerSeries (ι v) K) (ρ : Pl → ℝ),
    (∀ v, MvPowerSeries.constantCoeff (hh v) = 0) →
    (∀ v, ∀ Fv : MvPowerSeries (ι v) K, InClass (p : K) (hh v) Fv → ‖jetPair (P v) Fv‖ ≤ ρ v) →
    ∀ U : MvPowerSeries (Σ v, ι v) K, Integral U →
      ‖jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (P v))
        ((∏ v, atPlace v (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh v)))) * U)‖ ≤
        ∏ v, ρ v

end Formalism.InvariantFactorPaths.G7
