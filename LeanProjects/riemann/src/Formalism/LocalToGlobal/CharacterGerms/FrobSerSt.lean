import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

def FrobSerSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C),
    (∀ i (μ : σ →₀ ℕ), V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i f))) →
    ∀ μ : σ →₀ ℕ, (∃ i, ¬ V.l ∣ μ i) → V.MM (MvPowerSeries.coeff μ f)

def FrobPowSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
    (∀ n, V.MM (PowerSeries.coeff (V.l * n) (f ^ V.l) - PowerSeries.coeff n f ^ V.l)) ∧
    ∀ m, ¬ V.l ∣ m → V.MM (PowerSeries.coeff m (f ^ V.l))

end Formalism.L2.FormalSeriesBounds
