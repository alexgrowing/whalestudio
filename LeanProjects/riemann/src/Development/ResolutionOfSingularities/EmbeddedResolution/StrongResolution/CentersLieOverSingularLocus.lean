import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
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

def CentersLieOverSingularLocus : Prop :=
  ∀ i, i < S.ambientLength → ∀ p : ↥(S.strictTransform i),
    p ∈ (((S.centerOffDetached i).support : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i)) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)

def totalSpaceToBase (j : ℕ) : S.totalSpace j ⟶ Y :=
  Nat.rec (motive := fun j => S.totalSpace j ⟶ Y) S.totalSpaceZeroIso.hom
    (fun j ih => S.transitionMap j ≫ ih) j

@[simp] theorem totalSpaceToBase_zero : S.totalSpaceToBase 0 = S.totalSpaceZeroIso.hom := rfl

@[simp] theorem totalSpaceToBase_succ (j : ℕ) :
    S.totalSpaceToBase (j + 1) = S.transitionMap j ≫ S.totalSpaceToBase j := rfl

theorem totalSpaceToBase_eq_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) (j : ℕ) :
    S.totalSpaceToBase j = (S.blowupSequence h).projectionToBase j := by
  induction j with
  | zero =>
      show S.totalSpaceZeroIso.hom = (S.blowupSequence h).projectionToBase 0
      rw [(S.blowupSequence h).projectionToBase_zero]
      rfl
  | succ j ih =>
      have hb : (S.blowupSequence h).transitionMapSucc j = S.transitionMap j := S.tower_map_succ j
      rw [totalSpaceToBase_succ, ih, (S.blowupSequence h).projectionToBase_succ, hb]
      rfl

theorem inl_comp_totalSpaceToBase (j : ℕ) :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ S.totalSpaceToBase j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  induction j with
  | zero =>
      show (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom
          = 𝟙 (S.strictTransform 0) ≫ S.strictTransformZeroToBase
      rw [Category.id_comp, strictTransformZeroToBase_def]
  | succ j ih =>
      rw [totalSpaceToBase_succ, ← Category.assoc, S.inl_comp_transitionMap j, Category.assoc, ih,
        strictTransformToZero_succ, Category.assoc]

theorem centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups)
    (hc : S.InducedCentersLieOverSingularLocus h) : S.CentersLieOverSingularLocus := by
  intro i hi p hp
  have : AlgebraicGeometry.QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have : AlgebraicGeometry.QuasiCompact
      ((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) :=
    inferInstance
  have hcomap : (S.centerOnTotalSpace i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    have hk := Blowup.ker_comp_coprod_inl_comap_inl (Y := S.discardedUnion i) (S.centerOffDetached i).subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι] at hk
    exact hk
  have hp2 : p ∈ ((S.centerOnTotalSpace i).comap
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)).support := by
    rw [hcomap]
    exact hp
  have hp3 : (coprod.inl : S.strictTransform i ⟶ S.totalSpace i).base p
      ∈ (S.centerOnTotalSpace i).support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mp hp2
  have hmem := hc i hi _ hp3
  have e : (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.blowupSequence h).projectionToBase i
      = S.strictTransformToZero i ≫ S.strictTransformZeroToBase := by
    rw [← S.totalSpaceToBase_eq_blowupSequence_projectionToBase h i]
    exact S.inl_comp_totalSpaceToBase i
  have key : ((S.blowupSequence h).projectionToBase i).base
      ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i).base p)
      = (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p :=
    congrArg (fun g : S.strictTransform i ⟶ Y => g.base p) e
  rw [← key]
  exact hmem

end AffineSpacePrincipalizationData

end FunctorialResolution.EmbeddedResolution

end
