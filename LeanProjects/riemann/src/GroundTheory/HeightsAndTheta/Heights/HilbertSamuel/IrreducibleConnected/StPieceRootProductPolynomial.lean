import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PieceRootProductPolynomial.Statement : Prop :=
  ∀ (n d N k : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    m.Monic → Q ≠ 0 →
    (∀ x ∈ Z, (m.map (eval (A *ᵥ x))).IsRoot (∑ j, c j * x j)) →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
    ∃ G : Polynomial (MvPolynomial (Fin d) ℂ), G.Monic ∧ G.natDegree = k ∧
      ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
        G.map (eval y) = ∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))

end GroundTheory.Heights₂.Heights.HilbertSamuel
