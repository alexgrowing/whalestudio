import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_eq_empty_of_comap_eq_empty {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.Surjective f] (J : B.IdealSheafData) (μ : ℕ)
    (h : orderAtLeastLocus (J.comap f) μ = ∅) : orderAtLeastLocus J μ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, rfl⟩ := f.surjective x
  have hmem : y ∈ orderAtLeastLocus (J.comap f) μ := by
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff J μ (f.base y)).mp hx)
      (orderAt_le_orderAt_comap f J y)
  rw [h] at hmem
  simp at hmem

namespace MaxContactFunctoriality

theorem OrderReductionHypotheses.dropTrivialBoundary {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T)
    {hinv : ComapIsoInvariance.{u}} {A : ℕ → PrincipalizationAssignment.{u}} {B : PrincipalizationAssignment.{u}}
    (hd : DescentHypotheses hinv P A B) : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := by
  refine ⟨?_, ?_, ?_, hd.valid_trim T h.valid⟩
  · have hdim := h.dim_prop
    rwa [← MaxContactReduction.dropTrivialBoundary_dim T] at hdim
  · intro x
    exact h.orderLE x
  · exact h.coSupport_nonempty

section

variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
  (B : PrincipalizationAssignment.{u})

theorem isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme) :
    (d.IsMarked T.structMap T.ideal T.mult T.boundary ↔
      d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
        (MaxContactCoverData.tunedMult T) T.boundary) ∧
    (d.IsMarked T.structMap T.ideal T.mult T.boundary →
      ∀ i ≤ d.length,
        orderAtLeastLocus (d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid)
            (MaxContactCoverData.tunedMult T) i) (MaxContactCoverData.tunedMult T) =
          orderAtLeastLocus (d.controlledTransform T.ideal T.mult i) T.mult) := by
  have := h.valid.charZero
  have := h.valid.smooth
  have := h.valid.locallyOfFiniteType
  have h2 := hd.tuning
  unfold IsMarkedIffBalancedTunedSheaf at h2
  have key := h2 T.base T.scheme T.structMap T.ideal T.mult h.valid.one_le_mult
    ⟨(orderLE_iff T.ideal T.mult).mpr h.orderLE, h.coSupport_nonempty⟩ T.boundary d
  exact ⟨key.1, key.2.1⟩

theorem exists_blowupSequenceData_isStrictPullback_cover (hstar : CoverSequenceProperties hinv P A)
    (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    ∃ (d : BlowupSequenceData T.scheme)
      (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary),
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
            (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups
          d.toSequenceOfBlowups ∧
        maxContactPrincipalization hinv A T =
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  obtain ⟨d0, hpb0⟩ := hstar.descends (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd)
  obtain ⟨d, hdesc⟩ :
      ∃ e : BlowupSequenceData (MaxContactReduction.dropTrivialBoundary T).scheme,
        MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))) = some e :=
    MaxContactCoverData.exists_descendStrictPullback_eq_some _ _ ⟨d0, hpb0⟩
  have hpb : IsStrictPullbackBlowupSeq
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups :=
    MaxContactCoverData.isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdesc
  have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
      (MaxContactReduction.dropTrivialBoundary T).boundary :=
    hd.isMarked (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d hpb
  have hm1 : d.IsMarked T.structMap T.ideal T.mult (MaxContactReduction.dropTrivialBoundary T).boundary :=
    ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d).1).mpr hm0
  have hm : d.IsMarked T.structMap T.ideal T.mult T.boundary :=
    hd.isMarked_of_trim T h.valid d T.ideal T.mult hm1
  refine ⟨d, hm, hpb, ?_⟩
  exact MaxContactCoverData.reduceOrder_eq_toMarkedSequence hinv T (lowerDimensionalFamily A T) h.valid
    h.orderAtLeastLocus_ne_empty (h.dropTrivialBoundary hd).valid d hdesc hm

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (_hdim : P T.krullDimSucc)
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hemp : orderAtLeastLocus T.ideal T.mult = ∅) :
    (maxContactPrincipalization hinv A T).length = 0 := by
  have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
    MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
  rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length]

theorem center_support_nonempty (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i < (maxContactPrincipalization hinv A T).length) :
    (↑((maxContactPrincipalization hinv A T).center i).support :
      Set ↥((maxContactPrincipalization hinv A T).schemeAt i)).Nonempty := by
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · exfalso
    have hb : maxContactPrincipalization hinv A T = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [hb, MaxContactCoverData.emptyMarkedSeq_length] at hi
    exact Nat.not_lt_zero i hi
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    have hstarseq : ∀ j : ℕ,
        j < (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.length →
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.center j ≠ ⊤ := by
      intro j hj
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      exact hstar.center_ne_top (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) j hj
    have hdseq := hpb.center_ne_top_of_forall_center_ne_top hstarseq
    rw [heq] at hi ⊢
    rw [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups] at hi ⊢
    exact (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mpr (hdseq i hi)

private theorem orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective {k : Type u} [Field k] {X' X : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X}
    (hflat : AlgebraicGeometry.Flat g) (hsurj : AlgebraicGeometry.Surjective g)
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun Z => Z.comap g) E))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hdiv : ∀ i < d.length, ∃ Bb,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * Bb = (d.controlledTransform I m i).comap (d.map i))
    (hres : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus (d.controlledTransform I m d.length) m = ∅ := by
  have := hflat
  have := hsurj
  have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap t D t.length le_rfl
  have hid : t.ideal t.length
      = (d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform t D hdiv t.length le_rfl
  have hlen : t.length = d.length := MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq t D
  have h0 : orderAtLeastLocus ((d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl)) m = ∅ := by
    rw [← hid]
    exact hres
  have h1 := orderAtLeastLocus_eq_empty_of_comap_eq_empty (t.strictPullbackComparisonMap D t.length le_rfl)
    (d.controlledTransform I m t.length) m h0
  rwa [hlen] at h1

theorem isResolution_of_orderAt_le_mult (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) :
    (maxContactPrincipalization hinv A T).IsResolution := by
  rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq]
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length, MarkedSequenceOfBlowups.ideal_zero,
      hinv.coSupport_comap, hemp, Set.preimage_empty]
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    have h' : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := h.dropTrivialBoundary hd
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    rw [heq]
    simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_length,
      BlowupSequenceData.toMarkedBlowupSequenceData_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_length]
    have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (MaxContactReduction.dropTrivialBoundary T).boundary :=
      hd.isMarked (MaxContactReduction.dropTrivialBoundary T) h' d hpb
    have htc := (isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).2
      ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).1.mpr hm0) d.length le_rfl
    have D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups := by
      rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
      exact hpb.toStrictPullbackBlowupSeq
    have key : orderAtLeastLocus (d.controlledTransform
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) d.length)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) = ∅ :=
      orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective (hd.flat_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (hd.surjective_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (I := MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (m := MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (E := (MaxContactReduction.dropTrivialBoundary T).boundary) (d := d)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T)))
        D hm0.divisible (hstar.resolves (MaxContactReduction.dropTrivialBoundary T) h')
    exact htc.symm.trans key

theorem orderAt_ideal_le_mult (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (_hdim : P T.krullDimSucc) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i ≤ (maxContactPrincipalization hinv A T).length)
    (x : ↥((maxContactPrincipalization hinv A T).schemeAt i)) :
    orderAt ((maxContactPrincipalization hinv A T).ideal i) x ≤ (T.mult : ℕ∞) :=
  hd.order_le T hv hord (maxContactPrincipalization hinv A T) i hi x

end

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
