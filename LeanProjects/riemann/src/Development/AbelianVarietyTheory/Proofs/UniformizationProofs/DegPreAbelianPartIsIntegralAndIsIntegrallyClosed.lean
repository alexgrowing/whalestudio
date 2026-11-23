import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk :
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
      [Algebra (FractionRing R) F], IsIntegral (DegPre.BF D F).left ∧
        ∀ y : (DegPre.BF D F).left, IsIntegrallyClosed ((DegPre.BF D F).left.presheaf.stalk y) := by
  intro R _ _ D F _ _
  have h₁ := D.P.isAb.smooth
  have h₂ := D.P.isAb.geomConnected
  let j : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := DegPre.jFR (R := R) F
  let g : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := pullback.fst j D.P.A.hom
  have hs : Smooth g := inferInstanceAs (Smooth (pullback.fst j D.P.A.hom))
  have hc : ConnectedSpace (DegPre.BF D F).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.P.A.hom) j
      (pullback.snd j D.P.A.hom) (pullback.fst j D.P.A.hom) (IsPullback.of_hasPullback j D.P.A.hom).flip
  exact ⟨isIntegral_of_smooth_field_of_connectedSpace g, fun y ↦
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ g hs).2.1 y).2⟩

end GlobalTheory
