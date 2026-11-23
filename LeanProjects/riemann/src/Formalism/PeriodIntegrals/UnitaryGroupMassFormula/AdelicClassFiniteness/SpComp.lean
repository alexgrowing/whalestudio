import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne

noncomputable section

namespace PIW.AdelClassFin

open scoped Matrix

theorem spComp : SpComp := by
  intro E _ k m P R hPR
  have hsurj : Function.Surjective (Matrix.toLin' P) := fun v =>
    ⟨R *ᵥ v, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
  have hrank : Module.finrank E (LinearMap.range (Matrix.toLin' P)) = k := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  rw [hrank, Module.finrank_fin_fun] at hsum
  have hker : Module.finrank E (LinearMap.ker (Matrix.toLin' P)) = m - k := by omega
  refine ⟨by omega, ?_⟩
  let b : Module.Basis (Fin (m - k)) E (LinearMap.ker (Matrix.toLin' P)) := Module.finBasisOfFinrankEq E _ hker
  have hU : ∀ y : Fin (m - k) → E,
      (Matrix.of fun i j => (b j : Fin m → E) i) *ᵥ y =
        ((b.equivFun.symm y : LinearMap.ker (Matrix.toLin' P)) : Fin m → E) := by
    intro y
    ext i
    rw [Module.Basis.equivFun_symm_apply]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Matrix.of fun i j => (b j : Fin m → E) i, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (LinearMap.mem_ker.mp (b j).2) i
    rw [Matrix.toLin'_apply] at h
    exact h
  · intro y y' h
    simp only [hU] at h
    exact b.equivFun.symm.injective (Subtype.ext h)
  · intro w hw
    refine ⟨b.equivFun ⟨w, LinearMap.mem_ker.mpr (by rw [Matrix.toLin'_apply]; exact hw)⟩, ?_⟩
    rw [hU, LinearEquiv.symm_apply_apply]

end PIW.AdelClassFin
