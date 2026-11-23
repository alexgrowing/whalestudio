import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open GlobalTheory.CechPic in

theorem exists_rigLB_extension_dedekind :
    ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ (X' : Scheme.{0}) (π : X' ⟶ G.left) (p : X' ⟶ Sp K), IsPullback π p G.hom (spMap (algebraMap R K)) → ∀ L : LB X', L.IsLB → ∃ L' : RigLB G, LBIso (L'.L.pull π) L := by
  intro R K _ _ _ _ _ A _ hA X' φ p hφ N hN
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, hLN⟩ := exists_lineBundle_extension_of_generalizing A.left X' φ
    (Flat.generalizingMap φ) hst N hN
  let e : Sp R ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hL' : (L.pull (A.hom ≫ e)).IsLB := pull_isLB hL _
  have hM : (LB.div L (L.pull (A.hom ≫ e))).IsLB := LB.isLB_div hL hL'
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen ((LB.div L (L.pull (A.hom ≫ e))).pull e), t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hM e)).1 ?_
    rw [cls_pull hM, cls_div hL hL', cls_pull hL, map_sub, ← pull_comp, ← Category.assoc, he,
      Category.id_comp, sub_self]
  refine ⟨⟨LB.div L (L.pull (A.hom ≫ e)), t, hM, ht⟩, (cls_eq_iff (pull_isLB hM φ) hN).1 ?_⟩
  have h0 : pull (spMap (algebraMap R K) ≫ e) (cls L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 (DVR.exists_gen_of_local L hL _ _)
  rw [cls_pull hM, cls_div hL hL', cls_pull hL, map_sub, ← pull_comp, ← Category.assoc, hφ.w,
    Category.assoc, pull_comp, h0, map_zero, sub_zero]
  exact (cls_eq_iff (pull_isLB hL φ) hN).2 hLN

end GlobalTheory.CM
