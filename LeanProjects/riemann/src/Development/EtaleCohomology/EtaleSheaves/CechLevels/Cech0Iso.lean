import Development.EtaleCohomology.EtaleSheaves.CechLevels.CechLevelsOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf

def cech0Iso (f : Arrow PSh) : f.cechNerve.obj (op (SimplexCategory.mk 0)) ≅ f.left where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f.hom (fun _ => 𝟙 _) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; rw [Fin.fin_one_eq_zero j]; rw [Category.assoc]; erw [WidePullback.lift_π, Category.comp_id]
    · rw [Category.assoc]; erw [WidePullback.lift_base, Category.id_comp]; exact WidePullback.π_arrow _ 0
  inv_hom_id := by erw [WidePullback.lift_π]

theorem level0 : Level0 := by
  intro A A' _ _ φ I
  refine ⟨Arrow.isoMk (cech0Iso _) (cech0Iso _) ?_⟩
  simp only [cech0Iso, psi, Arrow.mk_hom, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]
  rfl

theorem CechLevels_of' (hL : Levels) : LateralTheory.E.t_E1Cut.CechLevels := CechLevels_of hL level0

end LateralTheory.E.CechLevelsPf
