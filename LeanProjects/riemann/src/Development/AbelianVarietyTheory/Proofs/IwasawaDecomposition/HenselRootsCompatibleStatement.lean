import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_roots_compatible : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V), IsLocalHom α → ∀ (θ : R) (η : V) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (q.map α).eval η = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) → ∃ ψ : R →+* V, ψ.comp φ = α ∧ IsLocalHom ψ := by
  first | exact @GlobalTheory.lift_of_compatible_approx | exact GlobalTheory.lift_of_compatible_approx | (intros; apply GlobalTheory.lift_of_compatible_approx <;> assumption)
