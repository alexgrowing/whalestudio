import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorial
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBExtDVR

theorem isOpenImmersion_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
    · exact IsUnit.mk0 _ (by
        simpa using (IsFractionRing.injective R K).ne_iff.2 hϖ.ne_zero)
    · intro z
      obtain ⟨⟨x, y, hy⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hy) hϖ
      refine ⟨n, x * ↑u⁻¹, ?_⟩
      simp only at h
      rw [map_mul, ← h, hu, _root_.mul_assoc, ← map_mul, ← map_pow]
      congr 2
      rw [mul_right_comm, Units.mul_inv, _root_.one_mul]
    · intro x y h
      exact ⟨0, by rw [IsFractionRing.injective R K h]⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem exists_lineBundle_extension_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X Y : Scheme.{0}) (s : X ⟶ Sp R) (t : Y ⟶ Sp K) (a : Y ⟶ X), Smooth s → QuasiCompact s → IsPullback a t s (spMap (algebraMap R K)) → ∀ L : LB Y, L.IsLB → ∃ M : LB X, M.IsLB ∧ LBIso (M.pull a) L := by
  intro R K _ _ _ _ _ _ X Y s t a hs hq hpb L hL
  haveI := isOpenImmersion_spMap_fractionRing R K
  have ha : IsOpenImmersion a := MorphismProperty.of_isPullback hpb.flip this
  haveI : IsRegularRing R := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth R s x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y a ha (fun x => (key x).1)
    (fun x => (key x).2) L hL

end GlobalTheory.LBExtDVR
