import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

theorem injStep : InjStep := by
  intro G _ N M π σ hirr T hT hne
  have hstab : ∀ g, ∀ v ∈ LinearMap.ker (Matrix.toLin' T),
      ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ LinearMap.ker (Matrix.toLin' T) := by
    intro g v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr _ hstab with h | h
  · obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' T) h
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    calc LinearMap.toMatrix' g * T = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' T) := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' T) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 1 := by rw [hg, LinearMap.toMatrix'_id]
  · have h0 : Matrix.toLin' T = 0 := LinearMap.ker_eq_top.mp h
    exact absurd (Matrix.toLin'.injective (h0.trans (map_zero _).symm)) hne

end PI.UnitaryGroupMassFormula.CommMult
