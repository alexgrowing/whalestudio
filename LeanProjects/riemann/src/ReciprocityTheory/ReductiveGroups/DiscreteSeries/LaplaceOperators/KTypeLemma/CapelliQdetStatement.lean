import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import Formalism.FormalDegreeBessel.StatementDS

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

universe u

def CapelliQdetStatement : Prop :=
  (∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (n : ℕ) (E : Fin n → Fin n → 𝒰) (x : ℂ),
    Capelli.capelliC E x = Formalism.REAL.qdet E x) ∧
  ∀ (n : ℕ) (lam : Fin n → ℝ) (ω : ℂ),
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (ω - ((n : ℂ) - 1) / 2) = ∏ t, (ω + ((thV lam t : ℝ) : ℂ))

def CentralCharStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (ω : ℂ), ∀ y ∈ genSub E V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y

def GapCentralStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), GapLap ε lam h →
    GapAtLeast ε lam h ∧ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧
      8 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) < h ∧
      8 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) < h

def HcVStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (ω : ℂ), ∀ y ∈ V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
