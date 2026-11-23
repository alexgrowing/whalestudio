import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isDominant_spMap_of_isFractionRing (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] : IsDominant (spMap (algebraMap T K)) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap T K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
  exact bot_le

theorem isDominant_genericFibre_of_flat (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f] :
    IsDominant (pullback.fst f (spMap (algebraMap T K))) := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  infer_instance

theorem connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

theorem isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := connectedSpace_of_flat_of_genericFibre T K f
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace X, hX.pred X⟩

theorem isIntegral_and_isNormalScheme_of_smooth_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom

end GlobalTheory
