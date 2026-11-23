import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GeometricallyConnectedOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfThickeningPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAlgebraizationGroupOperationsCdvrStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAbelianScheme_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsCommMonObj (Y e)) → IsProjBy B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e) := by
  intro V _ _ _ _ Y _ β hβ B b hA hc hP hb hβb
  have hprop : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hP
  have hsm : Smooth B.hom := by
    refine GlobalTheory.SmoothLimit.main V B fun e ↦ ?_
    have h : Smooth (Y e).hom := (hA e).smooth
    have he : (thickObj V (IsLocalRing.maximalIdeal V) e B).hom =
        (hb e).isoPullback.inv ≫ (Y e).hom := ((hb e).isoPullback_inv_snd).symm
    have h' : Smooth ((hb e).isoPullback.inv ≫ (Y e).hom) := inferInstance
    exact he ▸ h'
  have hconn : GeometricallyConnected B.hom :=
    GlobalTheory.ConnFibre.geometricallyConnected_of_closedFibre V B hsm hP (Y 0) (b 0) (hb 0)
      (hA 0).geomConnected
  obtain ⟨mu, io, un, H⟩ := GlobalTheory.T.exists_algebraization_group_operations_cdvr V Y β hβ B b hP inferInstance hb hβb
  obtain ⟨G, hG, hcomm⟩ := GlobalTheory.grpObj_of_thickenings V Y β hβ B b hb hβb mu io un H
  exact ⟨G, hcomm hc, ⟨hcomm hc, hsm, hprop, hconn⟩, hG⟩

end GlobalTheory
