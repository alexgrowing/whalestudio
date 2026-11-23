import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

def Facts {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (X : Dec ε lam π) : Prop :=
  (∀ s, s ∈ X.S ↔ Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) ∧ ∀ s, X.κ s = (lam s : ℂ) + ((m : ℂ) - 1) / 2

def DecLe : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), (∃ a, ε a = false) →
    (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) →
    ∃ X : Dec ε lam π, Facts X

def FlipDS : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)), IsDS (fun a => !ε a) lam σ ↔ IsDS ε lam σ

def FlipDec : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (X : Dec (fun a => !ε a) lam π), Facts X → ∃ Y : Dec ε lam π, Facts Y

end PositivityTheory.RgHe.Dec
