import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.IsoAwayFromCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

def schemeAtToSpec (i : ℕ) : S.ambientLevel i ⟶ Spec (CommRingCat.of k) :=
  S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec

@[simp] theorem schemeAtToSpec_def (i : ℕ) :
    S.schemeAtToSpec i = S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec := rfl

def boundary (i : ℕ) : List (S.ambientLevel i).IdealSheafData := S.principalizationSequence.boundary i

theorem boundary_def (i : ℕ) : S.boundary i = S.principalizationSequence.boundary i := rfl

def strictTransformToZero (i : ℕ) : S.strictTransform i ⟶ S.strictTransform 0 :=
  Nat.rec (motive := fun j => S.strictTransform j ⟶ S.strictTransform 0) (𝟙 _)
    (fun j ih => S.strictTransformMap j ≫ ih) i

@[simp] theorem strictTransformToZero_zero : S.strictTransformToZero 0 = 𝟙 (S.strictTransform 0) := rfl

@[simp] theorem strictTransformToZero_succ (i : ℕ) :
    S.strictTransformToZero (i + 1) = S.strictTransformMap i ≫ S.strictTransformToZero i := rfl

def strictTransformZeroToBase : S.strictTransform 0 ⟶ Y :=
  (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom

theorem strictTransformZeroToBase_def :
    S.strictTransformZeroToBase = (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom := rfl

theorem strictTransformZeroToBase_comp : S.strictTransformZeroToBase ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
  have hemb : S.emb ≫ S.ambientToSpec = pY := S.emb_comp
  have hz : S.ambientBlowups.projectionToBase 0 = S.ambientBlowups.isoZero.hom :=
    SequenceOfBlowups.projectionToBase_zero S.ambientBlowups
  have hspec := S.totalSpaceZeroIso_spec
  calc S.strictTransformZeroToBase ≫ pY
      = (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫ pY := by
        rw [strictTransformZeroToBase_def, Category.assoc]
    _ = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv)) ≫
          (S.ambientBlowups.isoZero.hom ≫ S.ambientToSpec) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hemb]
    _ = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
        rw [hspec, schemeAtToSpec_def, hz]

def detachedToBase (i : ℕ) : S.discardedSubscheme i ⟶ Y :=
  S.discardedι i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase

theorem detachedToBase_def (i : ℕ) :
    S.detachedToBase i = S.discardedι i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase := rfl

def StrictTransformEmptyAtLast : Prop := S.strictTransformIdeal S.ambientLength = ⊤

def DetachedSmooth : Prop :=
  ∀ i, i < S.ambientLength →
    AlgebraicGeometry.Smooth (S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i)

def SmoothLocusPreimageDenseInDetached : Prop :=
  ∀ i, i < S.ambientLength →
    Dense ((S.detachedToBase i).base ⁻¹' (pY.smoothLocus : Set ↥Y))

def InducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups) : Prop :=
  (S.blowupSequence h).CentersLieOver ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)

def DetachedClopenInCenter : Prop :=
  ∀ i, i < S.ambientLength →
    ∃ (T : (S.ambientCenter i).subscheme.Opens),
      IsClosed ((T : Set ↥((S.ambientCenter i).subscheme))) ∧
      ∃ e : S.discardedSubscheme i ≅ T.toScheme,
        e.hom ≫ T.ι ≫ (S.ambientCenter i).subschemeι = S.discardedι i ≫ S.strictTransformι i

def DetachedComponentsNotInBoundary : Prop :=
  ∀ i, i < S.ambientLength → ∀ (j : ℕ) (hj : j < (S.boundary i).length),
    ∀ C ∈ irreducibleComponents ↥(S.discardedSubscheme i),
      ¬ ((S.discardedι i ≫ S.strictTransformι i).base '' C ⊆
        ((((S.boundary i).get ⟨j, hj⟩).support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) :
          Set ↥(S.ambientLevel i)))

def DetachedSingularPreimageEqBoundary : Prop :=
  ∀ i, i < S.ambientLength →
    (S.detachedToBase i).base ⁻¹' ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) =
      (S.discardedι i ≫ S.strictTransformι i).base ⁻¹'
        (⋃ D ∈ S.boundary i,
          ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)))

def CentersHaveStrictNormalCrossingsWithBoundary : Prop :=
  ∀ i, i < S.ambientLength → HasStrictNormalCrossingsWith (S.schemeAtToSpec i) (S.ambientCenter i) (S.boundary i)

def AllLevelsSmooth : Prop :=
  ∀ i, i ≤ S.ambientLength → AlgebraicGeometry.Smooth (S.schemeAtToSpec i)

def BoundaryInStrictNormalCrossingPosition : Prop :=
  ∀ i, i ≤ S.ambientLength → InStrictNormalCrossingPosition (S.schemeAtToSpec i) (S.boundary i)

theorem inl_comp_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) (j : ℕ) :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  induction j with
  | zero =>
    have h0 : (S.blowupSequence h).projectionToBase 0 = S.totalSpaceZeroIso.hom :=
      SequenceOfBlowups.projectionToBase_zero (S.blowupSequence h)
    rw [h0, S.strictTransformToZero_zero, Category.id_comp, S.strictTransformZeroToBase_def]
  | succ j ih =>
    have hdown : (S.blowupSequence h).transitionMap (Nat.le_succ j) = S.transitionMap j := by
      rw [SequenceOfBlowups.transitionMap_def]
      exact S.tower_map_succ j
    have hd := (S.blowupSequence h).transitionMap_comp_projectionToBase (Nat.le_succ j)
    rw [hdown] at hd
    have e1 : (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫
          (S.blowupSequence h).projectionToBase (j + 1)
        = ((coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ S.transitionMap j)
            ≫ (S.blowupSequence h).projectionToBase j :=
      ((Category.assoc (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1))
            (S.transitionMap j) ((S.blowupSequence h).projectionToBase j)).trans
        (congrArg (fun f : S.totalSpace (j + 1) ⟶ Y =>
          (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ f) hd)).symm
    have e2 : ((coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ S.transitionMap j)
            ≫ (S.blowupSequence h).projectionToBase j
        = (S.strictTransformMap j ≫ (coprod.inl : S.strictTransform j ⟶ S.totalSpace j))
            ≫ (S.blowupSequence h).projectionToBase j :=
      congrArg (fun g : S.strictTransform (j + 1) ⟶ S.totalSpace j =>
        g ≫ (S.blowupSequence h).projectionToBase j) (S.inl_comp_transitionMap j)
    have e3 : (S.strictTransformMap j ≫ (coprod.inl : S.strictTransform j ⟶ S.totalSpace j))
            ≫ (S.blowupSequence h).projectionToBase j
        = S.strictTransformMap j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j)
            ≫ (S.blowupSequence h).projectionToBase j) :=
      Category.assoc _ _ _
    have e4 : S.strictTransformMap j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j)
            ≫ (S.blowupSequence h).projectionToBase j)
        = S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformZeroToBase) :=
      congrArg (fun g : S.strictTransform j ⟶ Y => S.strictTransformMap j ≫ g) ih
    have e5 : S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformZeroToBase)
        = S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase := by
      rw [S.strictTransformToZero_succ j, Category.assoc]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end AffineSpacePrincipalizationData

def AffineStrictTransformEmptyAtLast (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).StrictTransformEmptyAtLast

def AffineDetachedSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth

def AffineSmoothLocusPreimageDenseInDetached (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).SmoothLocusPreimageDenseInDetached

def AffineCentersLieOverSingularLocus (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).InducedCentersLieOverSingularLocus (hPrincipalization k Y pY)

def AffineDetachedClopenInCenter (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter

def AffineDetachedComponentsNotInBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedComponentsNotInBoundary

def AffineDetachedSingularPreimageEqBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary

def AffineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersHaveStrictNormalCrossingsWithBoundary

def AffineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).AllLevelsSmooth

def AffineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).BoundaryInStrictNormalCrossingPosition

private theorem smooth_from_initial {Z : Scheme.{u}} (f : (⊥_ Scheme.{u}) ⟶ Z) :
    AlgebraicGeometry.Smooth f := by
  have hf : f = initial.to Z := initial.hom_ext _ _
  rw [hf]
  infer_instance

private theorem preimage_comp_base_eq_preimage_preimage {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (W : Set ↥C) :
    (f ≫ g).base ⁻¹' W = f.base ⁻¹' (g.base ⁻¹' W) := by
  ext x
  simp

private theorem dense_of_isEmpty {α : Type u} [TopologicalSpace α] [IsEmpty α]
    (T : Set α) : Dense T := fun x => isEmptyElim x

private theorem isStrictNormalCrossingsDivisor_of_isEmpty {X : Scheme.{u}} (hX : IsEmpty ↥X)
    (D : X.IdealSheafData) : IsStrictNormalCrossingsDivisor D := fun x => (hX.false x).elim

private theorem smooth_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g)
    (hg : AlgebraicGeometry.Smooth g) : AlgebraicGeometry.Smooth f := by
  rw [h]
  exact hg

private theorem dense_preimage_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g) (W : Set ↥Z)
    (hg : Dense (g.base ⁻¹' W)) : Dense (f.base ⁻¹' W) := by
  rw [h]
  exact hg

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g)
    (W : TopologicalSpace.Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor (reducedInverseImage g W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage f W) := by
  rw [h]
  exact hg

private theorem dense_of_dense_preimage_inl_inr {A B : Scheme.{u}} (T : Set ↥(A ⨿ B))
    (hA : Dense ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' T))
    (hB : Dense ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' T)) : Dense T := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨z, hz⟩ := hne
  by_cases hzl : z ∈ Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base
  · obtain ⟨a, ha⟩ := hzl
    have hopen : IsOpen ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' U) :=
      hU.preimage (Scheme.Hom.continuous _)
    have hne2 : ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' U).Nonempty := by
      refine ⟨a, ?_⟩
      rw [Set.mem_preimage, ha]
      exact hz
    obtain ⟨x, hxU, hxT⟩ := (dense_iff_inter_open.mp hA) _ hopen hne2
    exact ⟨(coprod.inl : A ⟶ A ⨿ B).base x, hxU, hxT⟩
  · have hzr : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hzl
    obtain ⟨b, hb⟩ := hzr
    have hopen : IsOpen ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' U) :=
      hU.preimage (Scheme.Hom.continuous _)
    have hne2 : ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' U).Nonempty := by
      refine ⟨b, ?_⟩
      rw [Set.mem_preimage, hb]
      exact hz
    obtain ⟨x, hxU, hxT⟩ := (dense_iff_inter_open.mp hB) _ hopen hne2
    exact ⟨(coprod.inr : B ⟶ A ⨿ B).base x, hxU, hxT⟩

private theorem dense_preimage_of_dense_preimage_inl_inr_comp {A B Z : Scheme.{u}} (g : A ⨿ B ⟶ Z) (W : Set ↥Z)
    (hA : Dense (((coprod.inl : A ⟶ A ⨿ B) ≫ g).base ⁻¹' W))
    (hB : Dense (((coprod.inr : B ⟶ A ⨿ B) ≫ g).base ⁻¹' W)) :
    Dense (g.base ⁻¹' W) := by
  refine dense_of_dense_preimage_inl_inr _ ?_ ?_
  · rwa [preimage_comp_base_eq_preimage_preimage] at hA
  · rwa [preimage_comp_base_eq_preimage_preimage] at hB

private theorem dense_preimage_coprod_desc {P Q Z : Scheme.{u}} (a : P ⟶ Z) (b : Q ⟶ Z)
    (W : Set ↥Z) (ha : Dense (a.base ⁻¹' W)) (hb : Dense (b.base ⁻¹' W)) :
    Dense ((coprod.desc a b).base ⁻¹' W) := by
  refine dense_preimage_of_dense_preimage_inl_inr_comp (coprod.desc a b) W ?_ ?_
  · rw [coprod.inl_desc]
    exact ha
  · rw [coprod.inr_desc]
    exact hb

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc {P Q Z : Scheme.{u}} (a : P ⟶ Z) (b : Q ⟶ Z)
    (W : TopologicalSpace.Closeds ↥Z)
    (ha : IsStrictNormalCrossingsDivisor (reducedInverseImage a W)) (hb : IsStrictNormalCrossingsDivisor (reducedInverseImage b W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (coprod.desc a b) W) := by
  refine IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod (coprod.desc a b) W ?_ ?_
  · rw [coprod.inl_desc]
    exact ha
  · rw [coprod.inr_desc]
    exact hb

private theorem smooth_of_isEmpty_left {A P Z : Scheme.{u}} (g : A ⨿ P ⟶ Z) (hA : IsEmpty ↥A)
    (hP : AlgebraicGeometry.Smooth ((coprod.inr : P ⟶ A ⨿ P) ≫ g)) :
    AlgebraicGeometry.Smooth g := by
  have hdesc : coprod.desc ((coprod.inl : A ⟶ A ⨿ P) ≫ g)
      ((coprod.inr : P ⟶ A ⨿ P) ≫ g) = g :=
    coprod.hom_ext (by rw [coprod.inl_desc]) (by rw [coprod.inr_desc])
  have hA' : AlgebraicGeometry.Smooth ((coprod.inl : A ⟶ A ⨿ P) ≫ g) := by
    have := hA
    exact Blowup.smooth_of_isEmpty _
  exact smooth_of_eq hdesc.symm (Blowup.smooth_coprod_desc _ _ hA' hP)

private theorem dense_preimage_of_isEmpty_left {A P Z : Scheme.{u}} (g : A ⨿ P ⟶ Z) (W : Set ↥Z)
    (hA : IsEmpty ↥A)
    (hP : Dense (((coprod.inr : P ⟶ A ⨿ P) ≫ g).base ⁻¹' W)) : Dense (g.base ⁻¹' W) := by
  have := hA
  exact dense_preimage_of_dense_preimage_inl_inr_comp g W (dense_of_isEmpty _) hP

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left {A P Z : Scheme.{u}} (g : A ⨿ P ⟶ Z)
    (W : TopologicalSpace.Closeds ↥Z) (hA : IsEmpty ↥A)
    (hP : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : P ⟶ A ⨿ P) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) :=
  IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod g W (isStrictNormalCrossingsDivisor_of_isEmpty hA _) hP

private theorem smooth_eqToHom_comp_comp {X₁ X₂ Z W : Scheme.{u}} (e : X₁ = X₂) (g : X₂ ⟶ Z)
    (p : Z ⟶ W) (hg : AlgebraicGeometry.Smooth (g ≫ p)) :
    AlgebraicGeometry.Smooth ((eqToHom e ≫ g) ≫ p) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem isProper_eqToHom_comp {X₁ X₂ Z : Scheme.{u}} (e : X₁ = X₂) (g : X₂ ⟶ Z)
    (hg : AlgebraicGeometry.IsProper g) : AlgebraicGeometry.IsProper (eqToHom e ≫ g) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem dense_preimage_eqToHom_comp {X₁ X₂ Z : Scheme.{u}} (e : X₁ = X₂) (g : X₂ ⟶ Z)
    (W : Set ↥Z) (hg : Dense (g.base ⁻¹' W)) : Dense ((eqToHom e ≫ g).base ⁻¹' W) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp {X₁ X₂ Z : Scheme.{u}} (e : X₁ = X₂)
    (g : X₂ ⟶ Z) (W : TopologicalSpace.Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor (reducedInverseImage g W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (eqToHom e ≫ g) W) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem image_mem_irreducibleComponents_of_continuous_inverse {α β : Type u} [TopologicalSpace α]
    [TopologicalSpace β] (f : α → β) (g : β → α) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    {C : Set β} (hC : C ∈ irreducibleComponents β) :
    g '' C ∈ irreducibleComponents α := by
  obtain ⟨hirr, hmax⟩ := hC
  refine ⟨hirr.image g hg.continuousOn, ?_⟩
  intro b hb hsub
  have hb' : IsIrreducible (f '' b) := hb.image f hf.continuousOn
  have hCsub : C ⊆ f '' b := by
    intro y hy
    exact ⟨g y, hsub ⟨y, hy, rfl⟩, hfg y⟩
  have hmax' := hmax hb' hCsub
  intro x hx
  exact ⟨f x, hmax' ⟨x, hx, rfl⟩, hgf x⟩

private theorem support_prod_eq_iUnion {X : Scheme.{u}} (L : List X.IdealSheafData) :
    ((L.prod.support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ⋃ D ∈ L, ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  induction L with
  | nil =>
      rw [Blowup.idealSheafData_prod_nil]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_top]
  | cons D E ih =>
      rw [Blowup.idealSheafData_prod_cons]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_mul, ih]

private theorem support_comap_eq_preimage {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData) :
    (((I.comap f).support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = f.base ⁻¹' ((I.support : TopologicalSpace.Closeds ↥Z) : Set ↥Z) := by
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]

private theorem isProper_projectionToBase (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) {X : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (s : SequenceOfBlowups X) :
    ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsProper (s.projectionToBase i) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [SequenceOfBlowups.projectionToBase_zero s]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < s.length := hn
      have : AlgebraicGeometry.IsNoetherian (s.schemeAt n) :=
        isNoetherian_schemeAt s n (le_of_lt hlt)
      have : AlgebraicGeometry.IsProper (s.projectionToBase n) := ih (le_of_lt hlt)
      have : AlgebraicGeometry.IsProper (s.transitionMapSucc n) :=
        hproper _ _ _ _ (s.isBlowupAlongIdealSheaf_blowupMorphism n hlt)
      have h1 : s.transitionMapSucc n ≫ s.projectionToBase n = s.projectionToBase (n + 1) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact s.transitionMap_comp_projectionToBase (Nat.le_succ n)
      rw [← h1]
      infer_instance

private theorem strictTransformToZero_comp_schemeAtToSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i : ℕ, S.strictTransformToZero i ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0 = S.strictTransformι i ≫ S.schemeAtToSpec i := by
  intro i
  induction i with
  | zero => rw [S.strictTransformToZero_zero, Category.id_comp]
  | succ j ih =>
      have h2 : S.ambientBlowupMorphism j ≫ S.ambientBlowups.projectionToBase j = S.ambientBlowups.projectionToBase (j + 1) := by
        rw [show S.ambientBlowupMorphism j = S.ambientBlowups.transitionMapSucc j from rfl, SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact S.ambientBlowups.transitionMap_comp_projectionToBase (Nat.le_succ j)
      have h1 : S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
        rw [S.schemeAtToSpec_def j, S.schemeAtToSpec_def (j + 1), ← Category.assoc, h2]
      calc S.strictTransformToZero (j + 1) ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0
          = S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0) := by
            rw [S.strictTransformToZero_succ j, Category.assoc]
        _ = S.strictTransformMap j ≫ S.strictTransformι j ≫ S.schemeAtToSpec j := by rw [ih]
        _ = (S.strictTransformMap j ≫ S.strictTransformι j) ≫ S.schemeAtToSpec j := by rw [Category.assoc]
        _ = (S.strictTransformι (j + 1) ≫ S.ambientBlowupMorphism j) ≫ S.schemeAtToSpec j := by rw [S.strictTransformMap_comp_strictTransformι]
        _ = S.strictTransformι (j + 1) ≫ (S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j) := by rw [Category.assoc]
        _ = S.strictTransformι (j + 1) ≫ S.schemeAtToSpec (j + 1) := by rw [h1]

private theorem detachedToBase_comp_eq {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ) :
    S.detachedToBase i ≫ pY = S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i := by
  rw [S.detachedToBase_def i, Category.assoc, Category.assoc, S.strictTransformZeroToBase_comp,
    strictTransformToZero_comp_schemeAtToSpec S i]

private theorem inr_comp_eq_coprod_desc {A₁ A₀ P Q Z : Scheme.{u}} (φ : Q ⟶ A₀)
    (τ : (A₁ ⨿ (P ⨿ Q)) ⟶ (A₀ ⨿ P)) (u : (A₁ ⨿ (P ⨿ Q)) ⟶ Z) (v : (A₀ ⨿ P) ⟶ Z)
    (w : Q ⟶ Z)
    (hτ : (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) ≫ τ
        = coprod.desc (coprod.inr : P ⟶ (A₀ ⨿ P)) (φ ≫ (coprod.inl : A₀ ⟶ (A₀ ⨿ P))))
    (hv : τ ≫ v = u)
    (hw : φ ≫ ((coprod.inl : A₀ ⟶ (A₀ ⨿ P)) ≫ v) = w) :
    (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) ≫ u
      = coprod.desc ((coprod.inr : P ⟶ (A₀ ⨿ P)) ≫ v) w := by
  rw [← hw, ← hv, ← Category.assoc (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) τ v, hτ]
  apply coprod.hom_ext <;> simp

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_detachedToBase {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY)
    (hClopen : S.DetachedClopenInCenter) (hNotInBoundary : S.DetachedComponentsNotInBoundary)
    (hSing : S.DetachedSingularPreimageEqBoundary) (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hLevels : S.AllLevelsSmooth) (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u})
    (i : ℕ) (hi : i < S.ambientLength) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (S.detachedToBase i) (smoothLocusComplement pY)) := by
  obtain ⟨T, hTclosed, e, he⟩ := hClopen i hi
  have : AlgebraicGeometry.Smooth (S.schemeAtToSpec i) := hLevels i (le_of_lt hi)
  have hoi : AlgebraicGeometry.IsOpenImmersion e.inv := inferInstance
  have hgf : ∀ x : ↥(S.discardedSubscheme i), e.inv.base (e.hom.base x) = x := by
    intro x
    simp
  have hfg : ∀ x : ↥(T.toScheme), e.hom.base (e.inv.base x) = x := by
    intro x
    simp
  have hmor : e.inv ≫ (S.discardedι i ≫ S.strictTransformι i) = T.ι ≫ (S.ambientCenter i).subschemeι := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hbase : ∀ x : ↥(T.toScheme),
      (S.discardedι i ≫ S.strictTransformι i).base (e.inv.base x)
        = (T.ι ≫ (S.ambientCenter i).subschemeι).base x := by
    intro x
    have hh := congrArg (fun f : T.toScheme ⟶ S.ambientLevel i => f.base x) hmor
    simpa using hh
  have hcond : ∀ D ∈ S.boundary i, ∀ C ∈ irreducibleComponents ↥(T.toScheme),
      ¬ ((T.ι ≫ (S.ambientCenter i).subschemeι).base '' C ⊆
        ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    intro D hD C hC hsub
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hD
    have hC' : e.inv.base '' C ∈ irreducibleComponents ↥(S.discardedSubscheme i) :=
      image_mem_irreducibleComponents_of_continuous_inverse e.hom.base e.inv.base
        (Scheme.Hom.continuous _) (Scheme.Hom.continuous _) hgf hfg hC
    have himg : (S.discardedι i ≫ S.strictTransformι i).base '' (e.inv.base '' C)
        = (T.ι ≫ (S.ambientCenter i).subschemeι).base '' C := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hbase x)
    have hoff := hNotInBoundary i hi j hj (e.inv.base '' C) hC'
    rw [List.get_eq_getElem] at hoff
    exact hoff (by rw [himg]; exact hsub)
  have hsnc1 := hsncClopen k (S.ambientLevel i) (S.schemeAtToSpec i) (S.boundary i) (S.ambientCenter i)
      (hBoundarySNC i (le_of_lt hi)) (hCentersSNC i hi) T hTclosed hcond
  have hpre : ∀ W : Set ↥(S.ambientLevel i),
      (T.ι ≫ (S.ambientCenter i).subschemeι).base ⁻¹' W
        = e.inv.base ⁻¹' ((S.discardedι i ≫ S.strictTransformι i).base ⁻¹' W) := by
    intro W
    ext x
    simp only [Set.mem_preimage]
    rw [← hbase x]
  have hJsupp : (((((S.boundary i).prod.comap
        (T.ι ≫ (S.ambientCenter i).subschemeι)).support) :
          TopologicalSpace.Closeds ↥(T.toScheme)) : Set ↥(T.toScheme))
      = (T.ι ≫ (S.ambientCenter i).subschemeι).base ⁻¹'
        (⋃ D ∈ S.boundary i,
          ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    rw [support_comap_eq_preimage, support_prod_eq_iUnion]
  have hrp : reducedInverseImage (e.inv ≫ S.detachedToBase i) (smoothLocusComplement pY)
      = ((S.boundary i).prod.comap (T.ι ≫ (S.ambientCenter i).subschemeι)).radical := by
    refine reducedInverseImage_eq_radical _ _ _ ?_
    rw [hJsupp, hpre, ← hSing i hi, preimage_comp_base_eq_preimage_preimage]
  refine IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective (reducedInverseImage (S.detachedToBase i) (smoothLocusComplement pY))
      (fun _ : Unit => T.toScheme) (fun _ => e.inv) (fun _ => hoi) ?_ ?_
  · intro x
    exact ⟨(), e.hom.base x, hgf x⟩
  · intro _
    rw [comap_reducedInverseImage_of_isOpenImmersion e.inv (S.detachedToBase i) (smoothLocusComplement pY), hrp]
    exact hsnc1

private theorem smooth_discardedUnion_comp {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
    (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hSmooth : S.DetachedSmooth) :
    ∀ j, j ≤ S.ambientLength → AlgebraicGeometry.Smooth (G j ≫ pY) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact smooth_from_initial (G 0 ≫ pY)
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      have e1 : G (j + 1) ≫ pY
          = coprod.desc (G j ≫ pY) (S.detachedToBase j ≫ pY) :=
        (congrArg (fun t : S.discardedUnion (j + 1) ⟶ Y => t ≫ pY) (hG j)).trans
          (coprod.desc_comp pY (G j) (S.detachedToBase j))
      refine smooth_of_eq e1 ?_
      refine Blowup.smooth_coprod_desc _ _ (ih (le_of_lt hj')) ?_
      exact smooth_of_eq (detachedToBase_comp_eq S j) (hSmooth j hj')

private theorem dense_preimage_smoothLocus_of_discardedUnion {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
    (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hDense : S.SmoothLocusPreimageDenseInDetached) :
    ∀ j, j ≤ S.ambientLength → Dense ((G j).base ⁻¹' (pY.smoothLocus : Set ↥Y)) := by
  intro j
  induction j with
  | zero =>
      intro _
      have : IsEmpty ↥(S.discardedUnion 0) := (inferInstance : IsEmpty ↥(⊥_ Scheme.{u}))
      exact dense_of_isEmpty _
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      refine dense_preimage_of_eq (hG j) _ ?_
      exact dense_preimage_coprod_desc _ _ _ (ih (le_of_lt hj')) (hDense j hj')

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY) (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hClopen : S.DetachedClopenInCenter) (hNotInBoundary : S.DetachedComponentsNotInBoundary)
    (hSing : S.DetachedSingularPreimageEqBoundary) (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hLevels : S.AllLevelsSmooth) (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) :
    ∀ j, j ≤ S.ambientLength → IsStrictNormalCrossingsDivisor (reducedInverseImage (G j) (smoothLocusComplement pY)) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact isStrictNormalCrossingsDivisor_of_isEmpty (inferInstance : IsEmpty ↥(⊥_ Scheme.{u}))
        (reducedInverseImage (G 0) (smoothLocusComplement pY))
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      refine isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq (hG j) _ ?_
      exact isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc _ _ _ (ih (le_of_lt hj'))
        (isStrictNormalCrossingsDivisor_reducedInverseImage_detachedToBase S hClopen hNotInBoundary hSing hCentersSNC hBoundarySNC hLevels
          hsncClopen j hj')

private theorem isStrongResolution_blowupSequenceWithoutIsos {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups)
    (hEmpty : S.StrictTransformEmptyAtLast) (hSmooth : S.DetachedSmooth) (hDense : S.SmoothLocusPreimageDenseInDetached)
    (hCenters : S.InducedCentersLieOverSingularLocus h) (hClopen : S.DetachedClopenInCenter)
    (hNotInBoundary : S.DetachedComponentsNotInBoundary) (hSing : S.DetachedSingularPreimageEqBoundary)
    (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hLevels : S.AllLevelsSmooth) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) :
    IsStrongResolution k Y pY (S.blowupSequenceWithoutIsos h) := by
  have : IsNoetherianRing ↑(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_locallyOfFiniteType pY
  have hFeq : ∀ j : ℕ, S.transitionMap j ≫ (S.blowupSequence h).projectionToBase j
      = (S.blowupSequence h).projectionToBase (j + 1) := by
    intro j
    have hdown : (S.blowupSequence h).transitionMap (Nat.le_succ j) = S.transitionMap j := by
      rw [SequenceOfBlowups.transitionMap_def]
      exact S.tower_map_succ j
    have hd := (S.blowupSequence h).transitionMap_comp_projectionToBase (Nat.le_succ j)
    rw [hdown] at hd
    exact hd
  have hWeq : ∀ j : ℕ, S.discardedι j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫
      (S.blowupSequence h).projectionToBase j) = S.detachedToBase j := by
    intro j
    rw [S.inl_comp_blowupSequence_projectionToBase h j]
    exact (S.detachedToBase_def j).symm
  have hGeq : ∀ j : ℕ,
      ((coprod.inr : S.discardedUnion (j + 1) ⟶ S.totalSpace (j + 1)) ≫
          (S.blowupSequence h).projectionToBase (j + 1))
        = coprod.desc ((coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫
            (S.blowupSequence h).projectionToBase j) (S.detachedToBase j) := fun j =>
    inr_comp_eq_coprod_desc (S.discardedι j) (S.transitionMap j) ((S.blowupSequence h).projectionToBase (j + 1))
      ((S.blowupSequence h).projectionToBase j) (S.detachedToBase j) (coprod.inr_desc _ _) (hFeq j) (hWeq j)
  have hStrictEmpty : IsEmpty ↥(S.strictTransform S.ambientLength) := by
    have h2 : Set.range ⇑(S.strictTransformι S.ambientLength)
        = (((S.strictTransformIdeal S.ambientLength).support : TopologicalSpace.Closeds ↥(S.ambientLevel S.ambientLength)) :
          Set ↥(S.ambientLevel S.ambientLength)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _
    have h3 : (((S.strictTransformIdeal S.ambientLength).support : TopologicalSpace.Closeds ↥(S.ambientLevel S.ambientLength)) :
        Set ↥(S.ambientLevel S.ambientLength)) = ∅ := by
      have h1 : S.strictTransformIdeal S.ambientLength = ⊤ := hEmpty
      simp [h1, AlgebraicGeometry.Scheme.IdealSheafData.support_top]
    rw [h3] at h2
    exact Set.range_eq_empty_iff.mp h2
  have hLastStruct : (S.blowupSequenceWithoutIsos h).lastStructMap
      = eqToHom (SequenceOfBlowups.withoutIsoBlowups_lastObj (S.blowupSequence h)) ≫ (S.blowupSequence h).lastStructMap :=
    SequenceOfBlowups.withoutIsoBlowups_lastStructMap (S.blowupSequence h)
  have hLastProjection : (S.blowupSequence h).lastStructMap = (S.blowupSequence h).projectionToBase S.ambientLength :=
    SequenceOfBlowups.lastStructMap_eq_projectionToBase (S.blowupSequence h)
  have hSmoothDiscarded : AlgebraicGeometry.Smooth
      (((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
        (S.blowupSequence h).projectionToBase S.ambientLength) ≫ pY) :=
    smooth_discardedUnion_comp S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hSmooth S.ambientLength le_rfl
  have hDenseDiscarded : Dense ((((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
      (S.blowupSequence h).projectionToBase S.ambientLength)).base ⁻¹' (pY.smoothLocus : Set ↥Y)) :=
    dense_preimage_smoothLocus_of_discardedUnion S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hDense S.ambientLength le_rfl
  have hSNCDiscarded : IsStrictNormalCrossingsDivisor (reducedInverseImage
      ((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
        (S.blowupSequence h).projectionToBase S.ambientLength) (smoothLocusComplement pY)) :=
    isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hClopen hNotInBoundary hSing hCentersSNC hBoundarySNC hLevels hsncClopen S.ambientLength le_rfl
  have hstruct : AlgebraicGeometry.Smooth ((S.blowupSequence h).projectionToBase S.ambientLength ≫ pY) := by
    refine smooth_of_isEmpty_left (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
      ((S.blowupSequence h).projectionToBase S.ambientLength ≫ pY) hStrictEmpty ?_
    exact smooth_of_eq (Category.assoc _ _ _).symm hSmoothDiscarded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLastStruct, hLastProjection]
    refine smooth_eqToHom_comp_comp _ _ _ ?_
    exact hstruct
  · rw [hLastStruct, hLastProjection]
    exact isProper_eqToHom_comp _ _
      (isProper_projectionToBase hproper (S.blowupSequence h) S.ambientLength le_rfl)
  · exact isIso_restrict_lastStructMap_smoothLocus pY _ (SequenceOfBlowups.withoutIsoBlowups_centersLieOver _ hCenters)
  · rw [hLastStruct, hLastProjection]
    refine dense_preimage_eqToHom_comp _ _ _ ?_
    exact dense_preimage_of_isEmpty_left (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
      _ _ hStrictEmpty hDenseDiscarded
  · exact SequenceOfBlowups.withoutIsoBlowups_centersLieOver _ hCenters
  · rw [hLastStruct, hLastProjection]
    refine isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp _ _ _ ?_
    exact isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left (A := S.strictTransform S.ambientLength)
      (P := S.discardedUnion S.ambientLength) _ _ hStrictEmpty hSNCDiscarded

theorem isStrongResolution_blowupSequenceWithoutIsos_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hEmpty : AffineStrictTransformEmptyAtLast A hemb hsnc hsm)
    (hSmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hDense : AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm)
    (hCenters : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization)
    (hClopen : AffineDetachedClopenInCenter A hemb hsnc hsm)
    (hNotInBoundary : AffineDetachedComponentsNotInBoundary A hemb hsnc hsm)
    (hSing : AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm)
    (hCentersSNC : AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm)
    (hLevels : AffineAllLevelsSmooth A hemb hsnc hsm)
    (hBoundarySNC : AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm)
    (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y],
      IsStrongResolution k Y pY
        ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (hPrincipalization k Y pY)) := by
  intro k _ _ Y pY _ _ _ _
  exact isStrongResolution_blowupSequenceWithoutIsos (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
    (hPrincipalization k Y pY) (hEmpty k Y pY) (hSmooth k Y pY) (hDense k Y pY) (hCenters k Y pY)
    (hClopen k Y pY) (hNotInBoundary k Y pY) (hSing k Y pY) (hCentersSNC k Y pY) (hLevels k Y pY)
    (hBoundarySNC k Y pY) hsncClopen hproper

end FunctorialResolution.EmbeddedResolution

end
