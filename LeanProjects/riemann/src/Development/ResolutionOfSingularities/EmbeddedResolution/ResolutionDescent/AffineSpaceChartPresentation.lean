import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem affineSpace_reindex_symm_comp_reindex {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e.symm : m → n) S ≫ AffineSpace.reindex (e : n → m) S =
      𝟙 (AffineSpace n S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

private theorem affineSpace_reindex_comp_reindex_symm {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e : n → m) S ≫ AffineSpace.reindex (e.symm : m → n) S =
      𝟙 (AffineSpace m S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

def affineSpaceIsoOfEquiv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := affineSpace_reindex_symm_comp_reindex e S
  inv_hom_id := affineSpace_reindex_comp_reindex_symm e S

@[simp]
theorem affineSpaceIsoOfEquiv_hom {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom = AffineSpace.reindex (e.symm : m → n) S := rfl

@[simp]
theorem affineSpaceIsoOfEquiv_inv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).inv = AffineSpace.reindex (e : n → m) S := rfl

theorem affineSpaceIsoOfEquiv_hom_comp_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom ≫ (AffineSpace m S ↘ S) = (AffineSpace n S ↘ S) := by
  simp [affineSpaceIsoOfEquiv, AffineSpace.reindex]

theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type u) [Field k] {n m : Type u} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  exact affineSpaceIsoOfEquiv_hom_comp_over e (Spec (CommRingCat.of k))

def uliftFinSumOneEquiv (n : ℕ) : ULift.{u, 0} (Fin n ⊕ Fin 1) ≃ ULift.{u, 0} (Fin (n + 1)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

def toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (n + 1))) :=
  φ.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom

theorem isClosedImmersion_toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    AlgebraicGeometry.IsClosedImmersion (toAffineSpaceOfAmbientIso G n φ) := by
  have h : AlgebraicGeometry.IsClosedImmersion
      (φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  exact h

theorem toAffineSpaceOfAmbientIso_comp_toSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    toAffineSpaceOfAmbientIso G n φ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))) =
      G.ambientStruct := by
  have h : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [h]
  simp only [Category.assoc]
  rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hφ]

theorem hasSmoothCoordCodim_toAffineSpaceOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u}
    [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (toAffineSpaceOfAmbientIso G n φ) 1 := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin 1)))
      (affineSpaceInl k n 1) 1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
  have h2 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) 1 :=
    h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv.{u} n))
  have hdef : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [hdef]
  exact h2.iso_hom_comp φ

def presentationOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n φ
  one_le_codimBound := le_rfl
  one_le_dim := Nat.succ_le_succ (Nat.zero_le n)
  isClosedImmersion_toAffine := isClosedImmersion_toAffineSpaceOfAmbientIso G n φ
  toAffine_comp := toAffineSpaceOfAmbientIso_comp_toSpec G n φ hφ
  locallyConstCodim := hasSmoothCoordCodim_toAffineSpaceOfAmbientIso hsm G n φ

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) (by exact Category.id_comp _)

end FunctorialResolution.EmbeddedResolution

end
