import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem sval_eq_zero_of_local_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, d.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : sval d r z J = 0 := by
  have e : gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) 0 = 0 := by
    rw [gs_eq r z _ (hJ.mem φ r), map_zero, map_zero]
  exact (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans e

theorem appTop_field_point_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have := Over.w (toUnit (TF (R := R) F))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.comp_id _).symm.trans this
  rw [e]
  have hi : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have hc := hi.comp hb
  intro a b hab
  apply hc
  have na := congrArg (fun q => q.hom a) n
  have nb := congrArg (fun q => q.hom b) n
  exact na.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hab).trans nb)

theorem pullB_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  intro R _ _ D F _ _ k f s h α
  have := D.P.smoothDim
  have : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  rw [← not_iff_not]
  simp only [not_exists, not_not]
  constructor
  · intro hs
    refine sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ (toUnit (TF (R := R) F))
      (appTop_field_point_injective R F) _ D.P.L D.P.isLB _ _ _ (f α) fun z J hJ => ?_
    exact (h α z J hJ).symm.trans (sval_eq_zero_of_local_eq_zero (s α) hs _ z J hJ)
  · intro hf
    refine sec_eq_zero_of_sval_eq_zero_of_app_injective (𝟙 _) (fun U a b hab => hab) D.P.L D.P.isLB _ _ (s α)
      fun z J hJ => ?_
    exact (h α z J hJ).trans (sval_eq_zero_of_local_eq_zero (f α) hf _ z J hJ)

end GlobalTheory
