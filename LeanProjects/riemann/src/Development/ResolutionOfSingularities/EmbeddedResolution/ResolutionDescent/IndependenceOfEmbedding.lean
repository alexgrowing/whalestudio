import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EnlargeAmbientSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def affineSpaceIndexedByIsoOfEquiv (k : Type u) [Field k] {N M : Type u} (σ : N ≃ M) :
    affineSpaceIndexedBy k M ≅ affineSpaceIndexedBy k N where
  hom := AffineSpace.reindex σ (Spec (CommRingCat.of k))
  inv := AffineSpace.reindex σ.symm (Spec (CommRingCat.of k))
  hom_inv_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.apply_symm_apply]
      simp
  inv_hom_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.symm_apply_apply]
      simp

private def uliftFinAddEquivUliftSum (n m : ℕ) :
    ULift.{u, 0} (Fin (n + m)) ≃ ULift.{u, 0} (Fin n ⊕ Fin m) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans Equiv.ulift.symm)

private theorem locallyOfFiniteType_affineSpaceIndexedByToSpec (k : Type u) [Field k] (N : Type u)
    [Finite N] : AlgebraicGeometry.LocallyOfFiniteType (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem quasiCompact_affineSpaceIndexedByToSpec (k : Type u) [Field k] (N : Type u) :
    AlgebraicGeometry.QuasiCompact (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem irreducibleSpace_affineSpaceIndexedBy (k : Type u) [Field k] (N : Type u) :
    IrreducibleSpace ↥(affineSpaceIndexedBy k N) := by
  have : IrreducibleSpace ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum k))
  infer_instance

private theorem flat_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : CategoryTheory.IsIso f) :
    AlgebraicGeometry.Flat f := by
  have := hf
  have : AlgebraicGeometry.IsOpenImmersion f := inferInstance
  infer_instance

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr (Alg : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k]
    [CharZero k] (X : Scheme.{u}) (q : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] [AlgebraicGeometry.LocallyOfFiniteType q]
    [AlgebraicGeometry.QuasiCompact q] (I J : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (hJ : NonzeroOnComponents J) (E F : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition q E)
    (hF : InStrictNormalCrossingPosition q F) (hIJ : I = J) (hEF : E = F) :
    (Alg k X q I hI E hE).toSequenceOfBlowups = (Alg k X q J hJ F hF).toSequenceOfBlowups := by
  subst hIJ
  subst hEF
  rfl

theorem smooth_affineSpaceIndexedByToSpec_finSumFin (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (n m : ℕ) :
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m))) := by
  have hs : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m)))) :=
    hsm k (n + m)
  have h : AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k)) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m))) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) := by
    simp [affineSpaceIndexedByToSpec]
  have : CategoryTheory.IsIso (AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k))) :=
    ⟨AffineSpace.reindex (uliftFinAddEquivUliftSum n m).symm (Spec (CommRingCat.of k)),
      (affineSpaceIndexedByIsoOfEquiv k (uliftFinAddEquivUliftSum n m)).hom_inv_id,
      (affineSpaceIndexedByIsoOfEquiv k (uliftFinAddEquivUliftSum n m)).inv_hom_id⟩
  have hiso : AlgebraicGeometry.Smooth
      (AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k))) :=
    inferInstance
  rw [← h]
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) _ _ hiso hs

theorem isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (Φ : D.ambient ≅ D'.ambient) (hΦ : Φ.hom ≫ D'.ambientStruct = D.ambientStruct)
    (hemb : D.emb ≫ Φ.hom = D'.emb) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact D'.emb := inferInstance
  have hiso : CategoryTheory.IsIso Φ.inv := ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have : AlgebraicGeometry.Flat Φ.inv := flat_of_isIso Φ.inv hiso
  have : AlgebraicGeometry.Smooth Φ.inv := inferInstance
  have hsq : D'.emb ≫ Φ.inv = D.emb := by
    rw [← hemb, Category.assoc, Φ.hom_inv_id, Category.comp_id]
  have hpbk : IsPullback (𝟙 Y) D'.emb D.emb Φ.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hsq]⟩
  have hker : D'.emb.ker = D.emb.ker.comap Φ.inv := ker_eq_comap_ker_of_isPullback_of_flat hpbk
  have hφp : Φ.inv ≫ D.ambientStruct = D'.ambientStruct := by
    rw [← hΦ, ← Category.assoc, Φ.inv_hom_id, Category.id_comp]
  have hI' : NonzeroOnComponents (D.emb.ker.comap Φ.inv) := by
    rw [← hker]
    exact D'.nonzeroOnComponents_ker
  have hpbseq := hAlg.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
    D.nonzeroOnComponents_ker ([] : List D.ambient.IdealSheafData) D.sncEmpty
    D'.ambient D'.ambientStruct Φ.inv hφp hI' D'.sncEmpty
  have hseq : (Alg k D'.ambient D'.ambientStruct D'.emb.ker D'.nonzeroOnComponents_ker
        ([] : List D'.ambient.IdealSheafData) D'.sncEmpty).toSequenceOfBlowups =
      (Alg k D'.ambient D'.ambientStruct (D.emb.ker.comap Φ.inv) hI'
        (List.map (fun Z => Z.comap Φ.inv) ([] : List D.ambient.IdealSheafData))
        D'.sncEmpty).toSequenceOfBlowups :=
    principalizationAlgorithm_toSequenceOfBlowups_congr Alg k D'.ambient D'.ambientStruct _ _ _ _ _ _ _ _ hker rfl
  have hpb2 : IsPullbackBlowupSequence Φ.inv (D'.toEmbeddedBlowupSequence Alg).ambientSeq
      (D.toEmbeddedBlowupSequence Alg).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, hseq]
    exact hpbseq
  have hpbemb : IsPullback (𝟙 Y) (D'.toEmbeddedBlowupSequence Alg).emb (D.toEmbeddedBlowupSequence Alg).emb Φ.inv :=
    hpbk
  have hisoC : CategoryTheory.IsIso
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have hflatC : AlgebraicGeometry.Flat
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    flat_of_isIso _ hisoC
  have hres : IsPullbackBlowupSequence (𝟙 Y) (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D')
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D) :=
    ChartFlatBaseChange.isPullbackBlowupSequence_inducedBlowupsWithoutIso
      (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence Alg) (D'.toEmbeddedBlowupSequence Alg) Φ.inv (𝟙 Y)
        hpbemb hpb2) (hw k Y p D) (hw k Y p D')
  exact (isomorphic_of_isPullbackSequenceOfBlowups_id _ _ hres
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization Alg hw k Y p D)).symm

def LocallyConstCodimImpliesConstantCodim : Prop :=
  ∀ (k : Type u) [Field k] (X X' : Scheme.{u}) (q : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ] (c : ℕ),
    HasSmoothCoordCodim q τ c → HasEtaleCoordCodim q τ c

def LinearEmbeddingsHaveLocallyConstCodim : Prop :=
  ∀ (k : Type u) [Field k] (n m : ℕ),
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInl k n m) m ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInrEmbedding k n m) n

theorem isomorphic_embeddedResolutionRuleOfPrincipalization (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hcod : LocallyConstCodimImpliesConstantCodim.{u})
    (hlin : LinearEmbeddingsHaveLocallyConstCodim.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (P : ClosedEmbeddingIntoAffineSpace D) (P' : ClosedEmbeddingIntoAffineSpace D') :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have hsA : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) :=
    hsm k P.dim
  have hsA' : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) :=
    hsm k P'.dim
  have hsB : AlgebraicGeometry.Smooth
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))) :=
    smooth_affineSpaceIndexedByToSpec_finSumFin hsm k P.dim P'.dim
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have hciL : AlgebraicGeometry.IsClosedImmersion (affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR : AlgebraicGeometry.IsClosedImmersion (affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have : AlgebraicGeometry.IsClosedImmersion (D.emb ≫ P.toAffine) := inferInstance
  have : AlgebraicGeometry.IsClosedImmersion (D'.emb ≫ P'.toAffine) := inferInstance
  have hker1 : NonzeroOnComponents (Scheme.Hom.ker (D.emb ≫ P.toAffine)) :=
    nonzeroOnComponents_ker_comp D.emb P.toAffine D.nonzeroOnComponents_ker
  have hker1' : NonzeroOnComponents (Scheme.Hom.ker (D'.emb ≫ P'.toAffine)) :=
    nonzeroOnComponents_ker_comp D'.emb P'.toAffine D'.nonzeroOnComponents_ker
  have hsnc1 : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
  have hsnc1' : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
  have hsncB : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      ([] : List
        (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
  have hcd1 : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      P.toAffine P.codimBound :=
    hcod k D.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.codimBound
      P.locallyConstCodim
  have hcd1' : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      P'.toAffine P'.codimBound :=
    hcod k D'.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.codimBound
      P'.locallyConstCodim
  have hker2 : NonzeroOnComponents
      (Scheme.Hom.ker ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D.emb ≫ P.toAffine) (affineSpaceInl k P.dim P'.dim) hker1
  have hker2' : NonzeroOnComponents
      (Scheme.Hom.ker ((D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D'.emb ≫ P'.toAffine) (affineSpaceInrEmbedding k P.dim P'.dim) hker1'
  have hcd2 : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim (hlin k P.dim P'.dim).1
  have hcd2' : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim (hlin k P.dim P'.dim).2
  have hciL2 : AlgebraicGeometry.IsClosedImmersion
      (show (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp
            hker1 hsnc1).ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR2 : AlgebraicGeometry.IsClosedImmersion
      (show (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp
            hker1' hsnc1').ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have e1 := D.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1 hsnc1
    P.codimBound P.one_le_codimBound hcd1
  have e2 := (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
      hsnc1).isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB
      P'.dim P'.one_le_dim hcd2
  have e1' := D'.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
    hsnc1' P'.codimBound P'.one_le_codimBound hcd1'
  have e2' := (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
      hsnc1').isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB
      P.dim P.one_le_dim hcd2'
  have hc1 : (D.emb ≫ P.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)) = p := by
    rw [Category.assoc, P.toAffine_comp, D.comp_eq]
  have hc2 : (D'.emb ≫ P'.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)) = p := by
    rw [Category.assoc, P'.toAffine_comp, D'.comp_eq]
  obtain ⟨Φ, hΦ1, hΦ2⟩ :=
    hcmp k Y p P.dim P'.dim (D.emb ≫ P.toAffine) (D'.emb ≫ P'.toAffine) hc1 hc2
  have hembL : (D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInl P.dim P'.dim (D.emb ≫ P.toAffine)) :=
    comp_affineSpaceInl P.dim P'.dim p (D.emb ≫ P.toAffine) hc1
  have hembR : (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInr P.dim P'.dim (D'.emb ≫ P'.toAffine)) :=
    comp_affineSpaceInrEmbedding P.dim P'.dim p (D'.emb ≫ P'.toAffine) hc2
  have hfin : ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim) ≫ Φ.hom =
      (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim := by
    rw [hembL, hembR]
    exact hΦ2
  have e3 := isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso Alg hAlg hw k Y p
    ((D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
        hsnc1).enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB)
    ((D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
        hsnc1').enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB)
    Φ hΦ1 hfin
  exact e1.trans (e2.trans (e3.trans (e1'.trans e2').symm))

theorem isIndependentOfPresentedEmbedding_of_locallyConstCodim (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hcod : LocallyConstCodimImpliesConstantCodim.{u})
    (hlin : LinearEmbeddingsHaveLocallyConstCodim.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding := by
  intro k _ _ Y p _ _ _ _ D D' P P'
  exact isomorphic_embeddedResolutionRuleOfPrincipalization Alg hAlg hw hsm hcmp hcod hlin k Y p D D' P P'

end FunctorialResolution.EmbeddedResolution

end
