import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyCoefficientIntegralTorusPoint
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_coefficient_integral_torusPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (lam : FractionRing V) (th : Fam D (FractionRing V) 1),
    famProj D (FractionRing V) 1 0 th = lam • termF D (FractionRing V) 1 0 θ →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (χ : D.X) (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b →
    ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w χ (th.s χ) x →
    ∀ z J, Good D.P.L z J →
      cst (FractionRing V) z x = cst (FractionRing V) z lam *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi χ) (jFK (R := V) (FractionRing V)) z J)).val *
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
          ((toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left) z J *
        (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.UT.CoefInt.coef_int | exact GlobalTheory.UT.CoefInt.coef_int | (intros; apply GlobalTheory.UT.CoefInt.coef_int <;> assumption)
