import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TwoPlaces

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.DworkPowerSeriesWeights (Integral mvExp serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open MvPowerSeries

def RelShape {K : Type} [NormedField K] [CharZero K] {P Z : Type} (x : P → MvPowerSeries Z K)
    (g : Z → MvPowerSeries Z K) (E : MvPowerSeries Z K) (Ψ : MvPowerSeries P K) : Prop :=
  ∀ (τ : Type) [Fintype τ] (U0 Φ : MvPowerSeries (P ⊕ τ) K) (Ψ' : MvPowerSeries τ K), Integral U0 →
    constantCoeff Φ = 0 → constantCoeff Ψ' = 0 →
    Simeq Φ (serAlong Sum.inl Ψ + serAlong Sum.inr Ψ') →
    ∃ U : MvPowerSeries (Z ⊕ τ) K, Integral U ∧
      subst (Sum.elim (fun p => serAlong Sum.inl (x p)) (fun t => (X (Sum.inr t) : MvPowerSeries (Z ⊕ τ) K)))
          (mvExp (-Φ) * U0) =
        subst (Sum.elim (fun z => serAlong Sum.inl (g z)) (fun t => (X (Sum.inr t) : MvPowerSeries (Z ⊕ τ) K))) U *
          serAlong Sum.inl E * serAlong Sum.inr (mvExp (-Ψ'))

end Formalism.L2.DIV.C
