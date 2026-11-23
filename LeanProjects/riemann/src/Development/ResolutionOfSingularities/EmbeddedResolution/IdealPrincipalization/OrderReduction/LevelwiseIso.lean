import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem strictTransform_top_eq_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z ⊤ = ⊤ := by
  have h := comap_le_strictTransform f Z (⊤ : X.IdealSheafData)
  have h2 : (⊤ : X'.IdealSheafData) ≤ Blowup.strictTransform f Z ⊤ := by
    refine le_trans ?_ h
    simp
  exact top_le_iff.mp h2

theorem BlowupSequenceData.iteratedStrictTransform_top {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) :
    d.iteratedStrictTransform i ⊤ = ⊤ := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.iteratedStrictTransform_zero]
      simp
  | succ i ih =>
      rw [BlowupSequenceData.iteratedStrictTransform_succ, ih, strictTransform_top_eq_top]

structure BlowupSequenceData.LevelwiseIso {X : Scheme.{u}} (s₁ s₂ : BlowupSequenceData X) where
  iso : ∀ i : ℕ, i ≤ s₁.length → (s₁.obj i ≅ s₂.obj i)
  length_eq : s₁.length = s₂.length
  zero_compat : (iso 0 (Nat.zero_le _)).hom ≫ s₂.isoZero.hom = s₁.isoZero.hom
  map_compat : ∀ (i : ℕ) (hi : i < s₁.length),
    (iso (i + 1) hi).hom ≫ s₂.map i = s₁.map i ≫ (iso i hi.le).hom
  center_compat : ∀ (i : ℕ) (hi : i < s₁.length),
    (s₂.center i).comap (iso i hi.le).hom = s₁.center i

structure BlowupSequenceData.LevelwiseIsoOver {Y₁ Y₂ : Scheme.{u}} (φ : Y₁ ≅ Y₂)
    (t₁ : BlowupSequenceData Y₁) (t₂ : BlowupSequenceData Y₂) where
  iso : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i)
  length_eq : t₁.length = t₂.length
  zero_compat : (iso 0 (Nat.zero_le _)).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom ≫ φ.hom
  map_compat : ∀ (i : ℕ) (hi : i < t₁.length),
    (iso (i + 1) hi).hom ≫ t₂.map i = t₁.map i ≫ (iso i hi.le).hom
  center_compat : ∀ (i : ℕ) (hi : i < t₁.length),
    (t₂.center i).comap (iso i hi.le).hom = t₁.center i

private theorem nontrivialPart_nil {X : Scheme.{u}} :
    MarkedIdealWithBoundary.nontrivialPart ([] : List X.IdealSheafData) = [] := rfl

end FunctorialResolution.EmbeddedResolution

end
