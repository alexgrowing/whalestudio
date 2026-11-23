import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem Sh_dn_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (v : Cn (box F) 0) :
    Sh F 0 (dn (box F) 0 v) = prA F (dl 0) (S0 F 0 v) - prA F (dl 1) (S0 F 0 v) := by
  have e0 : bv F ((sI (0 : Fin 1)).comp (dl 0)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 0)) v =
      bv F ((dl (0 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have e1 : bv F ((sI (0 : Fin 1)).comp (dl 1)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 1)) v =
      bv F ((dl (1 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have hS : Sh F 0 = (bv F (sI (0 : Fin 1)) (Fin.predAboveOrderHom (0 : Fin 1))).toLinearMap :=
    (Fin.sum_univ_one (M := Cn (box F) 1 →ₗ[R] Bi F 1 0)
      fun i : Fin 1 ↦ ((-1 : R) ^ (i : ℕ)) • (bv F (sI i) (Fin.predAboveOrderHom i)).toLinearMap).trans (by simp)
  have hd : dn (box F) 0 v = pr (box F) (dl 0) v - pr (box F) (dl 1) v := by
    rw [dn_eq]
    refine (Fin.sum_univ_two (M := Cn (box F) 1)
      fun i : Fin 2 ↦ ((-1 : R) ^ (i : ℕ)) • pr (box F) (dl i) v).trans ?_
    simp [sub_eq_add_neg]
  simp only [S0, prA_bv]
  rw [← e0, ← e1, hS, hd, AlgHom.toLinearMap_apply, map_sub, bv_pr, bv_pr]

end GlobalTheory.CompanionTheory.HopfC
