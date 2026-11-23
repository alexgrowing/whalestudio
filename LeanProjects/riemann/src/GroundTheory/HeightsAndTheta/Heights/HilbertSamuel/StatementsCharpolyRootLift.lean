import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def CharpolyRootLift.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      l j ≠ 0 → c 0 = 1 → (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) →
      (LinearMap.charpoly (Algebra.lmul P Ω (u / l j ^ m))).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      ∀ (a : Fin (D + 1)) (hu : u / l a ^ m ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω)
        (ζ : Fin (D + 1) → ℂ), ζ a ≠ 0 → ∀ w : ℂ,
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank P Ω - i) = 0 →
        ∃ ψ : integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω →+* ℂ,
          (∀ (k : Fin (D + 1)) (hk : l k / l a ∈
              integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω),
            ψ ⟨l k / l a, hk⟩ = ζ k / ζ a) ∧
          ψ ⟨u / l a ^ m, hu⟩ = w / ζ a ^ m

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
