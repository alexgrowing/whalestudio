import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tower (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') (l : BC F F'')
    (h : ∀ T b, l.α T b = n.α T (m.α T b)) (x : S ⊗[R] C1 F) :
    th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  have hcomp : ∀ f : GlobalTheory.CatCoh.C1 F,
      GlobalTheory.CompanionTheory.PerfVB.c1 l f =
        GlobalTheory.CompanionTheory.PerfVB.c1 n (GlobalTheory.CompanionTheory.PerfVB.c1 m f) := by
    intro f
    simp only [GlobalTheory.CompanionTheory.PerfVB.c1, LinearMap.coe_mk, AddHom.coe_mk, h]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s f =>
    simp only [GlobalTheory.CompanionTheory.PerfVB.th1, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', GlobalTheory.CompanionTheory.PerfVB.liftSemi_tmul, LinearMap.map_smulₛₗ, hcomp]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CompanionTheory.PerfVB
