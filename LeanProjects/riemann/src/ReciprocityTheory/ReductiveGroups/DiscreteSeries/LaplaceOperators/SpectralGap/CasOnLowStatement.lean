import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def vogSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + (2 : ℝ) • rhoC ε)

def VogDropStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam →
    ∀ a b : Fin n, a < b → ε a ≠ ε b →
      vogSq ε (lowK ε lam - root a b) < vogSq ε (lowK ε lam)

def CasOnLowStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsInfUnitary ε E → StdGap ε lam →
    IsKIrrHW ε E (lowK ε lam) V →
    (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k (v : H)) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ S : Submodule ℂ D, ¬ IsKIrrHW ε E (lowK ε lam - root a b) S) →
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

end ReciprocityTheory.ChartRestriction.DS.Lap
