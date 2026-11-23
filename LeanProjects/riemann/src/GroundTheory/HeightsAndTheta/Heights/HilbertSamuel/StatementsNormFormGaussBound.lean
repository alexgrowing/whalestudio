import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def NormFormGaussBound.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ p : ℕ, p.Prime → ∀ (j : Fin (D + 1)) (K d : ℕ) (x : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      (c (Module.finrank P Ω)).IsHomogeneous d →
      (LinearMap.charpoly (Algebra.lmul P Ω x)).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      (p : Ω) ^ K * x ∈ integralClosure
        (Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})) Ω →
      ∀ μ : Fin (D + 1) →₀ ℕ,
        -((Module.finrank P Ω * K : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
