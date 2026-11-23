import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BasicOpenClosedEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedLocalChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothLocalChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.LastCoordinateSlices
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isZariskiLocalAtSource_locallyOfFiniteType :
    IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) := by
  have hrh : HasRingHomProperty (@LocallyOfFiniteType.{u}) RingHom.FiniteType := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) _ hrh

private theorem isZariskiLocalAtSource_flat :
    IsZariskiLocalAtSource (@Flat.{u}) := by
  have hrh : HasRingHomProperty (@Flat.{u}) RingHom.Flat := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Flat.{u}) _ hrh

private theorem locallyOfFiniteType_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, LocallyOfFiniteType (f i)) :
    LocallyOfFiniteType (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_locallyOfFiniteType
  exact IsZariskiLocalAtSource.sigmaDesc hf

private theorem flat_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Flat (f i)) : Flat (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_flat
  exact IsZariskiLocalAtSource.sigmaDesc hf

private theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) (hu : u ≫ pY = pV)
    (ι : Type u) [Fintype ι] [DecidableEq ι] (pt : ι → ↥V)
    (ch : ∀ i, PresentedLocalChart P H u r (pt i))
    (N : ℕ) (hN : ∀ i, (ch i).threshold ≤ N)
    (hcov : (⨆ i, (ch i).chartDomain) = ⊤) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      AlgebraicGeometry.IsAffine V'' ∧ AlgebraicGeometry.IsReduced V'' ∧
      AlgebraicGeometry.LocallyOfFiniteType pV'' ∧ AlgebraicGeometry.QuasiCompact pV'' ∧
      AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        AlgebraicGeometry.Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        AlgebraicGeometry.Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hsubs : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hDaff : ∀ i, IsAffine (((ch i).chartDomain).toScheme) := fun i =>
    (ch i).isAffineOpen_chartDomain
  have hambaff : ∀ i, IsAffine ((ch i).ambient) := fun i => (ch i).isAffine_ambient
  have hBaff : ∀ i, IsAffine ((H.ambient.basicOpen ((ch i).func)).toScheme) := fun i =>
    (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
  have hVaff : IsAffine (sigmaOpens V fun i => (ch i).chartDomain) :=
    isAffine_sigmaOpens V _ fun i => (ch i).isAffineOpen_chartDomain
  have hVcs : CompactSpace ↥(sigmaOpens V fun i => (ch i).chartDomain) := inferInstance
  obtain ⟨e, he⟩ : ∃ e : ι → k, Function.Injective e := by
    refine ⟨fun i => ((Fintype.equivFin ι i : ℕ) : k), fun a b hab => ?_⟩
    have h2 : (Fintype.equivFin ι a : ℕ) = (Fintype.equivFin ι b : ℕ) := Nat.cast_injective hab
    exact (Fintype.equivFin ι).injective (Fin.eq_of_val_eq h2)
  refine ⟨sigmaOpens V (fun i => (ch i).chartDomain),
    (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV,
    sigmaOpensDesc V (fun i => (ch i).chartDomain),
    hVaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton .., inferInstance,
    surjective_sigmaOpensDesc V _ hcov, rfl, ?_, ?_⟩
  · have hpullbackG : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
        ((sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u)
        (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb := by
      have h0 : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
          (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb :=
        isPullback_sigmaMap_sigmaDesc G.emb (fun i => (ch i).ambient)
          (fun i => ((ch i).chartDomain).toScheme) (fun i => (ch i).imm)
          (fun i => ((ch i).chartDomain).ι ≫ u) (fun i => (ch i).toAmbient)
          (fun i => (ch i).isPullback)
      have hdescu : (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u := by
        refine Limits.Sigma.hom_ext _ _ fun i => ?_
        simp
      rwa [hdescu] at h0
    have hsmfG : Smooth (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      smooth_sigmaDesc _ fun i => (ch i).smooth_toAmbient
    have hstructeq : (Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct
        = Limits.Sigma.desc fun i => (ch i).ambientStruct := by
      refine Limits.Sigma.hom_ext _ _ fun i => ?_
      simp [(ch i).comp_eq]
    have hsmstructG :
        Smooth ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact smooth_sigmaDesc _ fun i => (ch i).smooth_ambientStruct
    have hlftstructG :
        LocallyOfFiniteType ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact locallyOfFiniteType_sigmaDesc _ fun i => (ch i).locallyOfFiniteType_ambientStruct
    have hGaff : IsAffine (∐ fun i => (ch i).ambient) := inferInstance
    have hGcs : CompactSpace ↥(∐ fun i => (ch i).ambient) := inferInstance
    have hqcstructG :
        QuasiCompact ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) :=
      quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembG : IsClosedImmersion (Limits.Sigma.map fun i => (ch i).imm) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackG.flip G.isClosedImmersion_emb
    have hqcGemb : QuasiCompact G.emb := inferInstance
    have hqcembG : QuasiCompact (Limits.Sigma.map fun i => (ch i).imm) :=
      quasiCompact_of_isPullback hpullbackG.flip
    have hflatfG : Flat (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      flat_sigmaDesc _ fun i => inferInstance
    have hkerG : (Limits.Sigma.map fun i => (ch i).imm).ker
        = G.emb.ker.comap (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackG.flip
    have hnzG : NonzeroOnComponents (Limits.Sigma.map fun i => (ch i).imm).ker := by
      rw [hkerG]
      exact NonzeroOnComponents.comap_of_flat G.nonzeroOnComponents_ker _
    have hcompG : (Limits.Sigma.map fun i => (ch i).imm) ≫
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackG.w, Category.assoc, G.comp_eq, Category.assoc, hu]
    refine ⟨embeddingDatumOfClosedImmersion (∐ fun i => (ch i).ambient)
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        (Limits.Sigma.map fun i => (ch i).imm) hnzG hcompG (hsnc _ _ hsmstructG),
      Limits.Sigma.desc fun i => (ch i).toAmbient, ⟨?_⟩, hsmfG, rfl, hpullbackG⟩
    have hpres : ∀ i, ∃ σ : (ch i).ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
        IsClosedImmersion σ ∧
        σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = (ch i).ambientStruct ∧
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
          (P.codimBound + (N - r) + 1) := fun i => (ch i).presentation N (hN i)
    choose σ hσCI hσcomp hσcod using hpres
    have hσCI' : ∀ i, IsClosedImmersion (σ i) := hσCI
    have hCIunionG :
        IsClosedImmersion (coproductSliceMap k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      isClosedImmersion_coproductSliceMap k (P.dim + N + 1) e he (fun i => (ch i).ambient) σ
    have hCIfinG :
        IsClosedImmersion (coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      inferInstance
    refine ⟨P.codimBound + (N - r) + 1 + 1, P.dim + N + 1 + 1,
      coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ, by omega, by omega,
      hCIfinG, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (P.dim + N + 1) e (fun i => (ch i).ambient) σ _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (ch j).ambient) i ≫
          ((Limits.Sigma.desc fun j => (ch j).toAmbient) ≫ G.ambientStruct) =
          σ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))
      simp [(ch i).comp_eq, hσcomp i]
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (P.dim + N + 1)
        (P.codimBound + (N - r) + 1) e he (fun i => (ch i).ambient) σ hσcod
  · have hpullbackH : IsPullback
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        (sigmaOpensDesc V fun i => (ch i).chartDomain)
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) H.emb :=
      isPullback_sigmaMap_sigmaDesc H.emb
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => ((ch i).chartDomain).toScheme)
        (fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func))
        (fun i => ((ch i).chartDomain).ι)
        (fun i => (H.ambient.basicOpen ((ch i).func)).ι)
        (fun i => (ch i).isPullback_morphismRestrict_basicOpen)
    have hsmg : Smooth (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      smooth_sigmaDesc _ fun i => inferInstance
    have hlftg : LocallyOfFiniteType
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hflatg : Flat (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      flat_sigmaDesc _ fun i => inferInstance
    have hHaff : IsAffine (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      isAffine_sigmaOpens H.ambient _ fun i =>
        (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
    have hHcs :
        CompactSpace ↥(sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hsmq : Smooth
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hlftq : LocallyOfFiniteType
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hqcq : QuasiCompact
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembH : IsClosedImmersion
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackH.flip H.isClosedImmersion_emb
    have hqcHemb : QuasiCompact H.emb := inferInstance
    have hqcembH : QuasiCompact
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      quasiCompact_of_isPullback hpullbackH.flip
    have hkerH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker
          = H.emb.ker.comap
            (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackH.flip
    have hnzH : NonzeroOnComponents
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker := by
      rw [hkerH]
      exact NonzeroOnComponents.comap_of_flat H.nonzeroOnComponents_ker _
    have hcompH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) ≫
          ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
            H.ambientStruct)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackH.w, Category.assoc, H.comp_eq]
    refine ⟨embeddingDatumOfClosedImmersion
        (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func))
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫ H.ambientStruct)
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        hnzH hcompH (hsnc _ _ hsmq),
      sigmaOpensDesc H.ambient (fun i => H.ambient.basicOpen ((ch i).func)), ⟨?_⟩, hsmg, rfl,
      hpullbackH⟩
    have hCIrho : ∀ i, IsClosedImmersion
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) :=
      fun i => inferInstance
    have hrhocomp : ∀ i,
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
          = (H.ambient.basicOpen ((ch i).func)).ι ≫ H.ambientStruct := by
      intro i
      rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
      exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k Q.dim Q.toAffine ((ch i).func) H.ambientStruct
        Q.toAffine_comp
    have hrhocod : ∀ i,
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1))))
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
          (Q.codimBound + 1) :=
      fun i => hasSmoothCoordCodim_basicOpenEmbedding hsm k Q.dim Q.codimBound Q.toAffine
        ((ch i).func) Q.locallyConstCodim
    have hCIunionH : IsClosedImmersion
        (coproductSliceMap k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      isClosedImmersion_coproductSliceMap k (Q.dim + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
    have hCIfinH : IsClosedImmersion
        (coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      inferInstance
    refine ⟨Q.codimBound + 1 + 1, Q.dim + 1 + 1,
      coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom),
      by omega, by omega, hCIfinH, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (Q.dim + 1) e
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (H.ambient.basicOpen ((ch j).func)).toScheme) i ≫
          ((sigmaOpensDesc H.ambient fun j => H.ambient.basicOpen ((ch j).func)) ≫
            H.ambientStruct) =
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
      rw [hrhocomp i]
      simp
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (Q.dim + 1) (Q.codimBound + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
        hrhocod

theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      AlgebraicGeometry.IsAffine V'' ∧ AlgebraicGeometry.IsReduced V'' ∧
      AlgebraicGeometry.LocallyOfFiniteType pV'' ∧ AlgebraicGeometry.QuasiCompact pV'' ∧
      AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        AlgebraicGeometry.Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        AlgebraicGeometry.Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hVcs : CompactSpace ↥V := inferInstance
  have hch : ∀ y : ↥V, Nonempty (PresentedLocalChart P H u r y) := fun y =>
    nonempty_presentedLocalChart hS hsm k Y V pY pV G P H u r hu y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : ↥V => ((((hch y).some.chartDomain) : V.Opens) : Set ↥V))
    (fun y => ((hch y).some.chartDomain).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, (hch x).some.mem_domain⟩)
  have hfin : Fintype { y : ↥V // y ∈ t } := FinsetCoe.fintype t
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : { y : ↥V // y ∈ t }, ((hch i.1).some).threshold ≤ N :=
    ⟨Finset.univ.sup fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold,
      fun i => Finset.le_sup
        (f := fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold) (Finset.mem_univ i)⟩
  refine exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts hsm k hsnc Y V pY pV G P H Q u r hu
    { y : ↥V // y ∈ t } (fun i => i.1) (fun i => (hch i.1).some) N hN ?_
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩

end FunctorialResolution.EmbeddedResolution

end
