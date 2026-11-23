import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isMaxContactHypersurface_comap_fieldBaseChange {k K : Type u} [Field k] [Field K]
    [CharZero k] [CharZero K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    [AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (Spec.map φ))]
    (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface K (pullback.snd p (Spec.map φ))
      (A.comap (pullback.fst p (Spec.map φ))) m
      (H.comap (pullback.fst p (Spec.map φ))) := by
  intro y
  obtain ⟨U, hU, hxU, hcase⟩ := h ((pullback.fst p (Spec.map φ)).base y)
  have hVaff : IsAffineOpen (pullback.fst p (Spec.map φ) ⁻¹ᵁ U) :=
    hU.preimage (pullback.fst p (Spec.map φ))
  refine ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff, hxU, ?_⟩
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j, hH, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [orderAtLeastLocus_comap_fieldBaseChange p φ A m, Set.disjoint_left]
      intro a ha ha'
      exact Set.disjoint_left.mp hdisj ha ha'
    · have h1 := restrictIdeal_comap (pullback.fst p (Spec.map φ)) H U
      rw [hHtop, Scheme.IdealSheafData.comap_top] at h1
      exact h1
  · right
    refine ⟨n, c.baseChange (isPullback_pullback_specMap p φ), j, ?_, ?_⟩
    · refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff
        (c.baseChange (isPullback_pullback_specMap p φ))
        (H.comap (pullback.fst p (Spec.map φ))) {j} ?_
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE H (pullback.fst p (Spec.map φ))
          ⟨U, hU⟩ ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff⟩ le_rfl,
        c.ideal_eq_span_coord hU H {j} hH, Ideal.map_span]
      simp only [Finset.coe_singleton, Set.image_singleton]
      rw [EtaleChart.baseChange_coord]
    · refine (isMaxContactCoord_iff_coord_mem K (pullback.snd p (Spec.map φ))
        (A.comap (pullback.fst p (Spec.map φ))) m hVaff
        (c.baseChange (isPullback_pullback_specMap p φ)) j).mpr ?_
      rw [maxContactIdeal_comap_fieldBaseChange p φ m A,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE (maxContactIdeal k p A m)
          (pullback.fst p (Spec.map φ)) ⟨U, hU⟩
          ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff⟩ le_rfl,
        EtaleChart.baseChange_coord]
      exact Ideal.mem_map_of_mem _ ((isMaxContactCoord_iff_coord_mem k p A m hU c j).mp hmc)

namespace OrderReductionFieldBaseChange

private theorem isMaxContactHypersurface_comap_specMapOfFieldHom (k L : Type u) [Field k] [Field L]
    [CharZero k] [CharZero L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p] (f : k →+* L)
    [hft : AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k L f))]
    (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface L (pullback.snd p (specMapOfFieldHom k L f))
      (A.comap (pullback.fst p (specMapOfFieldHom k L f))) m
      (H.comap (pullback.fst p (specMapOfFieldHom k L f))) := by
  revert hft
  rw [specMapOfFieldHom_eq k L f]
  intro hft
  exact @isMaxContactHypersurface_comap_fieldBaseChange k L _ _ _ _ X p _ _
    (CommRingCat.ofHom f) hft A m H h

private theorem inStrictNormalCrossingPosition_comap_specMapOfFieldHom (k L : Type u) [Field k] [Field L]
    {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (f : k →+* L)
    (H : X.IdealSheafData) (hsnc : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k L f))
      [H.comap (pullback.fst p (specMapOfFieldHom k L f))] := by
  rw [specMapOfFieldHom_eq k L f]
  exact inStrictNormalCrossingPosition_comap_pullback_specMap p (CommRingCat.ofHom f) [H] hsnc

theorem maxContactHypersurfaceBaseChange : MaxContactHypersurfaceBaseChange.{u} := by
  intro S L instL instCZ f hV hV' H hadm hsnc
  refine ⟨?_, ?_⟩
  · rw [S.baseChange_structureMorphism L f, S.baseChange_ideal L f, S.baseChange_mult L f]
    intro hlft
    exact @isMaxContactHypersurface_comap_specMapOfFieldHom S.base L S.instField instL hV.charZero
      instCZ S.scheme S.structMap hV.smooth hV.locallyOfFiniteType f hlft S.ideal S.mult H
      (@hadm hV.locallyOfFiniteType)
  · rw [S.baseChange_structureMorphism L f]
    exact @inStrictNormalCrossingPosition_comap_specMapOfFieldHom S.base L S.instField instL S.scheme S.structMap
      hV.smooth f H hsnc

end OrderReductionFieldBaseChange

end FunctorialResolution.EmbeddedResolution

end
