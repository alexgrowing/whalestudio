import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.PsiZero

theorem psi_zero_mul_rigK : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  intro V _ _ D hB Z r z J hJ

  let T : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (TK V).hom)
  let ρ : T ⟶ TK V := Over.homMk r rfl
  have hcub : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) r z J = 1 := by
    have e := val_cub D.cub ρ hJ (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0)
    refine e.trans ?_
    rw [GlobalTheory.Poinc.ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face 1 1
  have hc := (val_mul hJ _ _ r).symm.trans ((val_corr hJ (hB 0 0 0) r).trans (val_mul hJ _ _ r))
  rw [hcub, _root_.mul_one,
    congrArg (fun w => val (D.tau w 0) r z J) (add_zero (0 : D.X))] at hc
  have ht : val (D.tau 0 0) r z J = 1 := (mul_eq_left.1 hc.symm)
  unfold DegPre.tau at ht
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) r z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul] at ht
  rw [← mul_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.Poinc.Sep.PsiZero
