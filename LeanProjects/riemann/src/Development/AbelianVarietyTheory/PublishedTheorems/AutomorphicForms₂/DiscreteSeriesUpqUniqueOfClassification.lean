import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)

theorem discreteSeriesUpqUnique_iff : DiscreteSeriesUpqUnique ↔ GlobalTheory.Dec.DSUnique :=
  ⟨fun h n ε lam H _ _ σ H' _ _ σ' hl hσ hσ' => h n ε lam hl H H' σ σ' hσ hσ',
    fun h n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => h n ε lam H σ H' σ' hl hσ hσ'⟩

theorem discreteSeriesUpqUnique_of_classification (h : GlobalTheory.DSId.DSClass) : DiscreteSeriesUpqUnique :=
  discreteSeriesUpqUnique_iff.2 (GlobalTheory.LowestKTypeDetermines.dsUnique_of_dsClass h)

end GlobalTheory.Published
