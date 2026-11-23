import Formalism.TorsionNormIteration.Statement

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT

open Formalism.G

def LTLemma : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (π : K), LTSetting K p q π →
    ∀ e e' : PowerSeries K, IsLTSeries q π e → IsLTSeries q π e' →
    ∀ (n : ℕ) (a : Fin n → K), (∀ i, ‖a i‖ ≤ 1) →
      ∃ φ : MvPowerSeries (Fin n) K, IntegralMv φ ∧ MvPowerSeries.constantCoeff φ = 0 ∧
        (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) φ = a i) ∧
        e.subst φ = MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i)) φ ∧
        ∀ ψ : MvPowerSeries (Fin n) K, MvPowerSeries.constantCoeff ψ = 0 →
          (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ = a i) →
          e.subst ψ = MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i)) ψ → ψ = φ

end Formalism.LT
