import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ShiftMap

theorem UpperTheory.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
          (p : G →* H), Continuous p → ∀ f : H → ℂ, Continuous f →
          FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : G => fun z : H => f ((p k)⁻¹ * z))) →
          ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), Continuous ρ ∧
            ∀ x : G →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ z, (x.sum fun k c => c * f ((p k)⁻¹ * z)) = 0 :=
  _root_.UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient
