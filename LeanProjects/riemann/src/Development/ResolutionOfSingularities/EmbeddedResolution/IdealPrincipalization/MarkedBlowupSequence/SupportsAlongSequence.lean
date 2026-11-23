import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem projectionToBase_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom := by
  have h0 : s.toSequenceOfBlowups.transitionMap (le_refl 0) = 𝟙 (s.toSequenceOfBlowups.schemeAt 0) := by
    rw [SequenceOfBlowups.transitionMap_def]
    have hid : (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (Opposite.op (0 : ℕ)) := rfl
    rw [hid, CategoryTheory.Functor.map_id]
  rw [SequenceOfBlowups.projectionToBase_def, h0, Category.id_comp]

theorem projectionToBase_succ_apply (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt (i + 1))) :
    (s.toSequenceOfBlowups.projectionToBase (i + 1)).base x =
      (s.toSequenceOfBlowups.projectionToBase i).base ((s.toSequenceOfBlowups.transitionMapSucc i).base x) := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i =
      s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [← h]
  rfl

theorem comap_ideal_le_ideal_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hi : i < s.toSequenceOfBlowups.length) :
    (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ≤ s.ideal (i + 1) := by
  rw [← s.ideal_succ i hi]
  exact fun U => Ideal.mul_le_right

theorem support_ideal_succ_subset_preimage (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hi : i < s.toSequenceOfBlowups.length) :
    (((s.ideal (i + 1)).support : Set ↥(s.toSequenceOfBlowups.schemeAt (i + 1)))) ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i).base ⁻¹'
        (((s.ideal i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i))) := by
  refine subset_trans (SetLike.coe_subset_coe.mpr
    (Scheme.IdealSheafData.support_antitone (s.comap_ideal_le_ideal_succ i hi))) ?_
  exact (Scheme.IdealSheafData.support_comap _ _).le

end MarkedSequenceOfBlowups

theorem MarkedIdealWithBoundary.IsAdmissible.isNoetherian {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) :
    AlgebraicGeometry.IsNoetherian T.scheme := by
  have : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : AlgebraicGeometry.QuasiCompact T.structMap := hV.quasiCompact
  have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base)) := inferInstance
  exact isNoetherian_of_locallyOfFiniteType T.structMap

end FunctorialResolution.EmbeddedResolution
