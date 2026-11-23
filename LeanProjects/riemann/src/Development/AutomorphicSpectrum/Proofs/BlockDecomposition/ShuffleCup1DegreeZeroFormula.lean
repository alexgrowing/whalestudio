import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem shuffle_cup1_degree_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (u : Cn (box F) 1) (w : Cn (box F) 0) :
    Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  have hsum : GlobalTheory.CompanionTheory.HopfC.Sh F 0 = AlgHom.toLinearMap
      (GlobalTheory.CompanionTheory.HopfC.bv F (N := 0 + 1) (p := 1) (q := 0)
        (GlobalTheory.CompanionTheory.HopfC.sI 0) (Fin.predAboveOrderHom 0)) := by
    rw [GlobalTheory.CompanionTheory.HopfC.Sh]
    first
    | (rw [Fin.sum_univ_one]; simp)
    | simp
    | (ext; simp)
  rw [hsum, AlgHom.toLinearMap_apply, GlobalTheory.CompanionTheory.HopfC.cup1_apply, map_mul,
    GlobalTheory.CompanionTheory.HopfC.bv_pr, GlobalTheory.CompanionTheory.HopfC.bv_pr]
  congr 1
  all_goals
    first
    | rfl
    | (refine GlobalTheory.CompanionTheory.HopfC.bv_congr (fun i => ?_) (fun i => ?_) _ <;>
        fin_cases i <;> first | rfl | decide | exact Subsingleton.elim (α := Fin 1) _ _)

end GlobalTheory.CompanionTheory.HopfC
