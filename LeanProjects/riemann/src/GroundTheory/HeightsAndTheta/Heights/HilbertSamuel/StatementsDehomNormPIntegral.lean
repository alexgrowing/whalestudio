import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomNormPIntegral.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (p : ℕ), p.Prime → ∀ M : ℕ, ¬ p ∣ M → ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      u ∈ integralClosure (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j))) Ω →
      ∀ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ,
        (c (Module.finrank P Ω)).IsHomogeneous (Module.finrank P Ω * m) →
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
        ∀ μ : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
