import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomCharpolyForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      (∀ k, u * (l j / l k) ^ m ∈ integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω) →
      ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, c 0 = 1 ∧
        (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) ∧
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) ∧
        (u ≠ 0 → c (Module.finrank P Ω) ≠ 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
