import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem isLocallyNoetherian_of_smooth_over_field (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q] :
    IsLocallyNoetherian Y :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian q

theorem smooth_projectionToBase_comp_and_orderAt_controlledTransform_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞))
    (t : ℕ) (ht : t ≤ d.length) :
    AlgebraicGeometry.Smooth (d.projectionToBase t ≫ p) ∧
      ∀ x : ↥(d.obj t), orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) := by
  revert ht
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.projectionToBase_zero]
        infer_instance
      · intro x
        rw [BlowupSequenceData.controlledTransform_zero, orderAt_comap_of_isOpenImmersion]
        exact hI _
  | succ s ih =>
      intro hs
      have hs' : s < d.length := hs
      obtain ⟨ihsm, ihord⟩ := ih (le_of_lt hs')
      have : AlgebraicGeometry.Smooth (d.projectionToBase s ≫ p) := ihsm
      have hπ : Blowup.IsBlowupAlongIdealSheaf (d.map s) (d.center s) := d.isBlowup s hs'
      have hsnc : HasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.boundaryFrom E s) := hd.center_snc s hs'
      have hsm1 : AlgebraicGeometry.Smooth (d.projectionToBase (s + 1) ≫ p) := by
        rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
      refine ⟨hsm1, ?_⟩
      have : AlgebraicGeometry.Smooth (d.projectionToBase (s + 1) ≫ p) := hsm1
      have : IsLocallyNoetherian (d.obj (s + 1)) :=
        isLocallyNoetherian_of_smooth_over_field k (d.projectionToBase (s + 1) ≫ p)
      have hIle : d.controlledTransform I m s ≤ (d.center s) ^ m :=
        le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.controlledTransform I m s) (d.boundaryFrom E s)
          hsnc m (hd.center_order s hs')
      have hEq : d.controlledTransform I m (s + 1)
          = controlledTransform (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle :=
        eq_controlledTransform_of_mul_eq_comap (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle
          (d.controlledTransform I m (s + 1)) (d.pow_exceptionalIdeal_mul_controlledTransform_succ I m s (hd.divisible s hs'))
      intro x
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le k (d.projectionToBase s ≫ p) (d.map s) (d.center s)
        (d.boundaryFrom E s) hsnc hπ (d.controlledTransform I m s) m hIle ihord x

theorem orderAt_controlledTransform_le_of_isMarked (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞))
    (t : ℕ) (ht : t ≤ d.length) (x : ↥(d.obj t)) :
    orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) :=
  (smooth_projectionToBase_comp_and_orderAt_controlledTransform_le k p I m E d hd hI t ht).2 x

end FunctorialResolution.EmbeddedResolution
