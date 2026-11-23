import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def ChartSpecCount.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ']
    (φ : R →+* Φ) (Q : Type) [Fintype Q] (r : Q → Φ'),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ E : R, φ E ≠ 0 ∧ ∀ ψ : R →+* ℂ, RingHom.ker φ ≤ RingHom.ker ψ → ψ E ≠ 0 →
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.Finite ∧
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.ncard =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0) → ∀ q, r q ≠ 0 → y q ≠ 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
