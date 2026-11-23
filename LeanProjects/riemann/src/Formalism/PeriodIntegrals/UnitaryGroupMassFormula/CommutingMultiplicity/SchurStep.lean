import Mathlib
import Formalism.PeriodIntegrals.UMultOne

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

def SchurStep : Prop :=
  ∀ (G : Type) [Group G] (M : ℕ) (σ : G →* GL (Fin M) ℂ), PI.UMultOne.Irr σ →
    ∀ C : Matrix (Fin M) (Fin M) ℂ,
      (∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * C = C * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      ∃ c : ℂ, C = c • (1 : Matrix (Fin M) (Fin M) ℂ)

def InjStep : Prop :=
  ∀ (G : Type) [Group G] (N M : ℕ) (π : G →* GL (Fin N) ℂ) (σ : G →* GL (Fin M) ℂ), PI.UMultOne.Irr σ →
    ∀ T : Matrix (Fin N) (Fin M) ℂ,
      (∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      T ≠ 0 → ∃ X : Matrix (Fin M) (Fin N) ℂ, X * T = 1

def AvStep : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    (N M : ℕ) (π : H →* GL (Fin N) ℂ) (σ : H →* GL (Fin M) ℂ),
    PI.UMultOne.Cont π → PI.UMultOne.Cont σ →
    ∀ (T : Matrix (Fin N) (Fin M) ℂ) (X : Matrix (Fin M) (Fin N) ℂ),
      (∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      X * T = 1 →
      ∃ S : Matrix (Fin M) (Fin N) ℂ,
        (∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * S = S * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) ∧
        S * T = 1

end PI.UnitaryGroupMassFormula.CommMult
