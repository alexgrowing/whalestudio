import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.lbIso_of_generic_semiAbelian_cdvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left), IsGrpPullback GK G₁ (jK V) φ → ∀ L L' : LB G₁.left, L.IsLB → L'.IsLB → LBIso (L.pull φ) (L'.pull φ) → LBIso L L' := by
  intro V _ _ _ hV G₁ _ _ hG GK _ φ hφ L L' hL hL' h
  haveI : IsDiscreteValuationRing V := hV.1
  have hi : pullback.fst G₁.hom (jK V) = hφ.1.isoPullback.inv ≫ φ := hφ.1.isoPullback_inv_fst.symm
  have h' : LBIso (L.pull (pullback.fst G₁.hom (jK V))) (L'.pull (pullback.fst G₁.hom (jK V))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.1.isoPullback.inv hi h
  exact GlobalTheory.lbIso_of_generic_normal_local V inferInstance inferInstance G₁.left G₁.hom (eSec G₁) hG.smooth
    hG.quasiCompact (GlobalTheory.geometricallyIntegral_of_isSemiAbelian G₁ (h := hG)) (Over.w (MonObj.one (X := G₁))) L L' hL hL' h'
