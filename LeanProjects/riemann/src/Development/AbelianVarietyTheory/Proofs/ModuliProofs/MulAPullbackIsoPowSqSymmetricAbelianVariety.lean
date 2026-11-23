import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.MulSym

open GlobalTheory.MulPull GlobalTheory.PrimNorm

theorem lbIso_mulPull_of_cube {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (M : LB A.left)
    (k : ℕ) (hM : M.IsLB) (hc : ∃ t : LB.Gen (Theta A M), t.IsGen) (hs : SymB M) :
    LBIso (M.pull (Out.mulA A k).left) (lbPow M (k ^ 2)) := by
  have hcube : HasGen M (thφ A (x3 A)) thε := hc
  have hrig : HasGen M (Y := Spec (CommRingCat.of K)) (K := PUnit) (fun _ => eSec A) (fun _ => 1) :=
    DVR.exists_gen_of_local M hM _ _
  have hs' : LBIso (M.pull (𝟙 A.left)) (M.pull (GrpObj.inv : A ⟶ A).left) :=
    LBIso.chartPull (chartPullPull M _ _ rfl) (chartPullId _) hs
  have hneg := (lbIso_iff hM _ _ _ _).1 hs'
  simp only [Fintype.prod_unique, zpow_one] at hneg
  have main := hasGen_pow hM hcube (𝟙 A) ?_ ?_ k
  · have h := (hasGen_iff hM _ _).1 main
    refine (lbIso_iff hM _ _ _ _).2 ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg_one,
      mul_inv_eq_one] at h
    simp only [Fintype.prod_unique, zpow_one, Nat.cast_pow]
    exact h.symm
  · refine (hrig.pull (toUnit A).left).of_formEq hM (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  · refine (hasGen_iff hM _ _).2 ?_
    have e : ((𝟙 A : A ⟶ A)⁻¹) = (GrpObj.inv : A ⟶ A) := Category.id_comp _
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg_one, zpow_one,
      mul_inv_eq_one, e]
    exact hneg

theorem lbIso_mulPull_of_symB : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ), M.IsLB → SymB M → LBIso (M.pull (Out.mulA P.A k).left) (lbPow M (k ^ 2)) :=
  fun _ _ _ P M k hM hs => lbIso_mulPull_of_cube P.A M k hM (GlobalTheory.AbLaw.CubeAssembly.cube_gen _ P M hM) hs

end GlobalTheory.MulSym
