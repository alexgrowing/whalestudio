import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalConverseGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ), 0 < m →
    ∀ π₁ π₂ : IrrRep (GL (Fin (m + 1)) k), IsCuspidal π₁.ρ → IsCuspidal π₂.ρ →
      (∀ τ : IrrRep (GL (Fin m) k), ∃ e : ℂ, HasPairEps ψ π₁.ρ τ.ρ e ∧ HasPairEps ψ π₂.ρ τ.ρ e) →
      Nonempty (π₁.ρ.Equiv π₂.ρ)

end GlobalTheory.Published

end
