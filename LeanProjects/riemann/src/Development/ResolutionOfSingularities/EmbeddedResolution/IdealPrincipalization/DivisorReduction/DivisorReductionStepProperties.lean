import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem topologicalKrullDim_ne_bot_of_nonempty (X : Scheme.{u}) [Nonempty ↥X] :
    topologicalKrullDim ↥X ≠ ⊥ := by
  intro hb
  have hb' : Order.krullDim (IrreducibleCloseds ↥X) = ⊥ := hb
  have hE : IsEmpty (IrreducibleCloseds ↥X) := Order.krullDim_eq_bot_iff.mp hb'
  obtain ⟨x⟩ := ‹Nonempty ↥X›
  exact hE.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

theorem one_le_krullDimSucc (X : Scheme.{u}) [Nonempty ↥X] : 1 ≤ krullDimSucc X := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (topologicalKrullDim_ne_bot_of_nonempty X)
  rw [← hn, withBotSuccToNat_coe]
  exact Nat.le_add_left 1 _

theorem krullDimSucc_eq_zero_of_isEmpty (X : Scheme.{u}) [IsEmpty ↥X] : krullDimSucc X = 0 := by
  have hE : IsEmpty (IrreducibleCloseds ↥X) := by
    constructor
    intro C
    obtain ⟨x, -⟩ := C.2.1
    exact isEmptyElim x
  have h : topologicalKrullDim ↥X = ⊥ := Order.krullDim_eq_bot_iff.mpr hE
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h, withBotSuccToNat_bot]

private theorem nonempty_homeomorph_subscheme_range_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) :
    Nonempty (↥D.subscheme ≃ₜ ↥(Set.range ⇑D.subschemeι)) :=
  ⟨(Scheme.Hom.isClosedEmbedding D.subschemeι).toIsEmbedding.toHomeomorph⟩

private theorem isClosed_range_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) :
    IsClosed (Set.range ⇑D.subschemeι) :=
  (Scheme.Hom.isClosedEmbedding D.subschemeι).isClosed_range

theorem krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor (X : Scheme.{u}) [Nonempty ↥X]
    (hfin : topologicalKrullDim ↥X < ⊤) (D : X.IdealSheafData) (hD : Blowup.IsLocallyGeneratedByNonZeroDivisor D) :
    krullDimSucc D.subscheme < krullDimSucc X := by
  rcases isEmpty_or_nonempty ↥D.subscheme with hem | hne
  · have := hem
    rw [krullDimSucc_eq_zero_of_isEmpty D.subscheme]
    exact lt_of_lt_of_le Nat.zero_lt_one (one_le_krullDimSucc X)
  · have := hne
    obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeι D
    have hrange : Set.range ⇑D.subschemeι = (D.support : Set ↥X) :=
      Scheme.IdealSheafData.range_subschemeι D
    refine krullDimSucc_lt_of_homeomorph_isClosed X D.subscheme (Set.range ⇑D.subschemeι)
      (isClosed_range_subschemeι D) ?_ ?_ hfin e
    · exact Set.range_nonempty _
    · intro C hC hsub
      rw [hrange] at hsub
      exact hD.not_irreducibleComponent_subset_support hC hsub

theorem isOpen_setOf_connectedComponent_subset {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (P : Set X) : IsOpen {x : X | connectedComponent x ⊆ P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, Blowup.isOpen_connectedComponent_of_noetherianSpace X x,
    mem_connectedComponent⟩
  intro y hy
  show connectedComponent y ⊆ P
  rw [← connectedComponent_eq hy]
  exact hx

theorem centersContainNoComponent_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hm : 1 ≤ T.mult)
    (s : T.SequenceOfBlowups) : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent :=
  MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence effectiveCartierSupportContainsNoComponent hV s

theorem isOpen_setOf_connectedComponent_subset_orderAtLeastLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult} := by
  have := hV.isNoetherian
  have hN : NoetherianSpace ↥T.scheme := inferInstance
  obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeι (T.boundary.get ⟨j, hj⟩)
  have : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_of_surjective _ e.symm.continuous e.symm.surjective
  exact isOpen_setOf_connectedComponent_subset _

private theorem get_mem_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
  simp

theorem dim_restrictToBoundaryDivisor_lt (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) :
    (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc := by
  obtain ⟨x, -⟩ := hne
  have : Nonempty ↥T.scheme := ⟨x⟩
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    hV.snc.1 _ (get_mem_boundary T j hj)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (T.boundary.get ⟨j, hj⟩) := hsd.1
  exact krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor T.scheme
    hV.topologicalKrullDim_lt_top (T.boundary.get ⟨j, hj⟩) hcart

structure DivisorReductionStepProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  exists_ideal_mul_preIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ J : T.scheme.IdealSheafData,
        DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal
  isMarked_pushedTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isBlowup_id_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
  valid_lowerTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible
  valid_lowerPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ∀ x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i),
          orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length + 1 →
        ∀ x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i),
          orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult s.length) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj s.length))) = ∅
  coSupport_inter_ker_eq_empty_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (s.length + 1)) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  isPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [AlgebraicGeometry.IsClosedImmersion σ]
      [AlgebraicGeometry.IsClosedImmersion σ'] [AlgebraicGeometry.Flat φ]
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [AlgebraicGeometry.IsClosedImmersion σ]
      [AlgebraicGeometry.IsClosedImmersion σ'] [AlgebraicGeometry.Flat φ]
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (i + 1)).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L), (T.baseChange L f).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.baseChange L f).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap
          (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.pullbackAlong Y q h).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData), T.mult = 1 →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      DivisorReduction.containedComponentsIdeal T j hj = ⊤
  smooth_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      AlgebraicGeometry.Smooth
        ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap)
  hasSNCWith_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary
  support_preIdeal_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆
        orderAtLeastLocus T.ideal T.mult

theorem DivisorReductionStepProperties.toDivisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (h : DivisorReductionStepProperties hres hno) :
    DivisorReductionTerminationProperties hres hno where
  exists_ideal_mul_preIdeal_pow := h.exists_ideal_mul_preIdeal_pow
  isMarked_pushedTop := h.isMarked_pushedTop
  isMarked_pushedPre := h.isMarked_pushedPre
  isBlowup_id_preIdeal := h.isBlowup_id_preIdeal
  lowerTriple_dim_lt := fun T hV hne j hj I₀ E₀ => dim_restrictToBoundaryDivisor_lt T hV hne j hj I₀ E₀
  valid_lowerTop := h.valid_lowerTop
  valid_lowerPre := h.valid_lowerPre
  orderAt_ctrlIdeal_le_top := h.orderAt_ctrlIdeal_le_top
  orderAt_ctrlIdeal_le_pre := h.orderAt_ctrlIdeal_le_pre
  coSupport_inter_ker_eq_empty_top := h.coSupport_inter_ker_eq_empty_top
  coSupport_inter_ker_eq_empty_pre := h.coSupport_inter_ker_eq_empty_pre
  properCenters := fun T hV hm s => centersContainNoComponent_of_isAdmissible T hV hm s
  isPullbackSeq_ambientTower := h.isPullbackSeq_ambientTower
  isStrictPullbackSeq_ambientTower := h.isStrictPullbackSeq_ambientTower
  comap_ctrlIdeal_top := h.comap_ctrlIdeal_top
  comap_ctrlIdeal_pre := h.comap_ctrlIdeal_pre
  preIdeal_baseChange := h.preIdeal_baseChange
  preIdeal_pullbackAlong := h.preIdeal_pullbackAlong
  preIdeal_eq_top_of_imageIdeal := h.preIdeal_eq_top_of_imageIdeal
  isOpen_preLocus := fun T hV j hj => isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  smooth_preIdeal := h.smooth_preIdeal
  hasSNCWith_preIdeal := h.hasSNCWith_preIdeal
  support_preIdeal_subset := h.support_preIdeal_subset

end FunctorialResolution.EmbeddedResolution

end
