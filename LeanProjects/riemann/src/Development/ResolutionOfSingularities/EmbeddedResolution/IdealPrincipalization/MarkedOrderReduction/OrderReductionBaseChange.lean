import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.RecursivePrincipalizationPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isNoetherian_schemeAt_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (u : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (i : ℕ) (hi : i ≤ u.length) :
    AlgebraicGeometry.IsNoetherian (u.obj i) := by
  have hlen : i ≤ u.toMarkedSequenceOfBlowups.length := hi.trans_eq (MarkedBlowupSequenceData.toMarkedSequence_length u).symm
  have h := MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT u.toMarkedSequenceOfBlowups i hlen
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h

private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_zero {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hflat : AlgebraicGeometry.Flat g) (sD : SequenceOfBlowups X) (sU : SequenceOfBlowups Y)
    (hD : sD.length = 0) (hU : sU.length = 0) :
    Nonempty (SequenceOfBlowupsPullback g sU sD) := by
  have := hflat
  refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq (SequenceOfBlowupsPullback.ofCentersMissImage g (BlowupSequenceData.ofSequenceOfBlowups sD) ?_
    (BlowupSequenceData.ofSequenceOfBlowups sU) ?_)⟩
  · intro i hi
    rw [BlowupSequenceData.ofSequenceOfBlowups_length sD, hD] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact (BlowupSequenceData.ofSequenceOfBlowups_length sU).trans hU

private theorem length_nonMonomialOrderReductionIter_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    (nonMonomialOrderReductionIter hinv T rc 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  have h : (nonMonomialOrderReductionIter hinv T rc 0).length = 0 := by
    rw [nonMonomialOrderReductionIter_zero, emptyMarkedBlowupSequenceData_length]
  exact (MarkedBlowupSequenceData.toMarkedSequence_length (nonMonomialOrderReductionIter hinv T rc 0)).trans h

private theorem markedDataOfSeq_ne_none_of_isMarked {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    markedDataOfSeq s J μ σ ≠ none := by
  have he : markedDataOfSeq s J μ σ = some ((MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData
      (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [he]
  exact Option.some_ne_none _

private theorem lastIdeal_and_boundary_comap_of_flat {k k' : Type u} [Field k] [Field k'] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')} {g : Y ⟶ X}
    {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E') (hm : m' = m)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hflat : AlgebraicGeometry.Flat g)
    (hI : I' = I.comap g)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (E.map fun D => D.comap g))
    (hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) := by
  subst hm
  have := hflat
  exact SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' c hI hE hN hN'

private theorem extendByNonMonomialPart_sequenceOfBlowupsPullback_cases (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (NonMonomialOrderReductionContinues T' s' ∧ Nonempty (SequenceOfBlowupsPullback g
        (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups)) ∨
      Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  obtain ⟨hlastIdeal, hsameBoundary⟩ :=
    lastIdeal_and_boundary_comap_of_flat s s' hmult c hbc.flat hideal hbdry
      (isNoetherian_schemeAt_of_isAdmissible T hT s) (isNoetherian_schemeAt_of_isAdmissible T' hT' s')
  have hle : maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s :=
    maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
      s s' c hlastIdeal hsameBoundary
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hJ : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT s hcont
  have hskip : orderAtLeastLocus ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) = ∅ →
      Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro hempty
    have hL : extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s
        = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) := rfl
    rw [hL]
    exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim hdim'
      hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      hJ hempty
  by_cases hcont' : NonMonomialOrderReductionContinues T' s'
  · by_cases heq : maxOrderNonMonomial T' s' = maxOrderNonMonomial T s
    · refine Or.inl ⟨hcont', ?_⟩
      refine nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart hG hinv n A B hspec T T' g hT hT' hdim
        hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hcont hcont' heq ?_
      intro h h'
      refine iff_of_false ?_ ?_
      · exact markedDataOfSeq_ne_none_of_isMarked s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) _
          (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)
      · have hmkU := isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT' hdim' s' hcont'
        rw [hnonMon, heq] at hmkU
        exact markedDataOfSeq_ne_none_of_isMarked s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) _
          hmkU
    · refine Or.inr (hskip ?_)
      exact orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT'
        hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lt_of_le_of_ne hle heq)
  · refine Or.inr (hskip ?_)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT'
        hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hlt
    · have h1 : T'.mult ≤ maxOrderNonMonomial T' s' := by
        rw [hmult, heq]
        exact ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
      have h2 : ¬ (orderAtLeastLocus (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')).Nonempty := fun hx =>
        hcont' ((nonMonomialOrderReductionContinues_iff T' s').2 ⟨h1, hx⟩)
      have h3 := Set.not_nonempty_iff_eq_empty.mp h2
      rw [hnonMon, heq] at h3
      exact h3

theorem nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').ideal
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length =
        ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).ideal
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        ((nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').boundary
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length)
        (((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).boundary
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).map fun D => D.comap c.lastMap) := by
  classical
  have key : ∀ j : ℕ, ∃ f' : ℕ, Nonempty (SequenceOfBlowupsPullback g
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro j
    induction j with
    | zero =>
        exact ⟨0, nonempty_sequenceOfBlowupsPullback_of_length_eq_zero g hbc.flat _ _
          (length_nonMonomialOrderReductionIter_zero hinv T (principalizationOfDimLe T A))
          (length_nonMonomialOrderReductionIter_zero hinv T' (principalizationOfDimLe T' A))⟩
    | succ j ih =>
        obtain ⟨f', hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j)
        · rcases extendByNonMonomialPart_sequenceOfBlowupsPullback_cases hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
            hideal hbdry hbc (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j)
            (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f') c hcont with ⟨hcont', hcmp⟩ | hcmp
          · refine ⟨f' + 1, ?_⟩
            rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) j hcont,
              nonMonomialOrderReductionIter_succ_of_continues hinv T' (principalizationOfDimLe T' A) f' hcont']
            exact hcmp
          · refine ⟨f', ?_⟩
            rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) j hcont]
            exact hcmp
        · refine ⟨f', ?_⟩
          rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) j hcont]
          exact ⟨c⟩
  obtain ⟨f', hc⟩ := key f
  obtain ⟨c⟩ := hc
  refine ⟨f', c, ?_⟩
  exact lastIdeal_and_boundary_comap_of_flat (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)
    (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f') hmult c hbc.flat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible T hT (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f))
    (isNoetherian_schemeAt_of_isAdmissible T' hT' (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f'))

private theorem lastIdeal_and_boundary_comap_of_isAdmissible (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hflat : AlgebraicGeometry.Flat g)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) :=
  lastIdeal_and_boundary_comap_of_flat s s' hmult c hflat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible T hT s) (isNoetherian_schemeAt_of_isAdmissible T' hT' s')

private theorem markedDataOfSeq_companionIdeal_ne_none (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) (K : (s.obj s.length).IdealSheafData) (ν : ℕ)
    (hK : companionIdeal T s = K) (hν : T.mult * maxOrderNonMonomialOnOrderLocus T s = ν)
    (h : (tripleAtLength T s K ν).krullDimSucc ≤ T.krullDimSucc) :
    ¬ (markedDataOfSeq s K ν (principalizationOfDimLe T A (tripleAtLength T s K ν) h) = none) := by
  subst hK
  subst hν
  exact markedDataOfSeq_ne_none_of_isMarked s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    (principalizationOfDimLe T A (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

private theorem nonempty_sequenceOfBlowupsPullback_nonMonomialOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) :
    Nonempty (SequenceOfBlowupsPullback g
      (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  obtain ⟨f₁, c, hI, hB⟩ := nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT
    hT' hdim hdim' hmult hideal hbdry hbc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)
  have hlow : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) :=
    (nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)).symm
  have hncT : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)) := by
    rw [hlow]
    exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  have hncT' : ¬ NonMonomialOrderReductionContinues T' (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁) := by
    intro hc
    exact hncT (nonMonomialOrderReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc
      (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (maxOrder (nonMonomialPart T.boundary T.ideal) + 1))
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁) c hI hB hc)
  have h1 : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A)
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1))
      = nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁ :=
    nonMonomialOrderReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A) f₁ hncT'
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1)) (le_max_left _ _)
  have h2 : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A)
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1))
      = nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A) :=
    nonMonomialOrderReductionIter_eq_of_maxOrder_lt hG hinv hspec hT' hdim'
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1)) (le_max_right _ _)
  have hup : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁ = nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A) :=
    h1.symm.trans h2
  refine ⟨?_⟩
  rw [← hup, ← hlow]
  exact c

theorem companionIdealReductionIter_exists_sequenceOfBlowupsPullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
          f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
          f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').ideal
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length =
        ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).ideal
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).comap
            c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        ((companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').boundary
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length)
        (((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).boundary
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).map
            fun D => D.comap c.lastMap) := by
  have hflat : AlgebraicGeometry.Flat g := hbc.flat
  have key : ∀ m : ℕ, ∃ f' : ℕ, Nonempty (SequenceOfBlowupsPullback g
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
        f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
        m).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro m
    induction m with
    | zero =>
        exact ⟨0, nonempty_sequenceOfBlowupsPullback_nonMonomialOrderReduction hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
          hideal hbdry hbc⟩
    | succ m ih =>
        obtain ⟨f₁, hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : CompanionIdealReductionContinues T
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
        · obtain ⟨hI, hB⟩ := lastIdeal_and_boundary_comap_of_isAdmissible T T' g hT hT' hflat hmult hideal hbdry
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
            (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c
          have hstepL := companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hcont
          have hle := maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
            hideal hbdry hbc
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
            (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
          rcases hle.lt_or_eq with hlt | heq
          · have hJ := companionTriple_isAdmissible hG hT
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hcont
            have hempty := orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt hG hinv n A
              T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              hlt
            refine ⟨f₁, ?_⟩
            rw [hstepL]
            exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT'
              hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              (companionIdeal T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
              (T.mult * maxOrderNonMonomialOnOrderLocus T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)) hJ hempty
          · have hcont1 : (1 : ℕ) ≤ maxOrderNonMonomialOnOrderLocus T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) := hcont
            have hcont' : CompanionIdealReductionContinues T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) := by
              show (1 : ℕ) ≤ maxOrderNonMonomialOnOrderLocus T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁)
              exact le_trans hcont1 heq.ge
            have hid' := companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim
              hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              heq
            have hmu' : T'.mult * maxOrderNonMonomialOnOrderLocus T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁)
                = T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) := by
              rw [hmult, heq]
            refine ⟨f₁ + 1, ?_⟩
            rw [hstepL, companionIdealReductionIter_succ_of_continues hinv T' (principalizationOfDimLe T' A)
              (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁ hcont']
            refine nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal hG hinv n A B hspec T T' g hT hT'
              hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              hcont hcont' heq ?_
            intro h h'
            refine iff_of_false ?_ ?_
            · exact markedDataOfSeq_companionIdeal_ne_none hG T hT A
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hcont
                (companionIdeal T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                (T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                rfl rfl h
            · exact markedDataOfSeq_companionIdeal_ne_none hG T' hT' A
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) hcont'
                ((companionIdeal T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)).comap
                    c.lastMap)
                (T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                hid' hmu' h'
        · refine ⟨f₁, ?_⟩
          rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hcont]
          exact ⟨c⟩
  obtain ⟨f', hn⟩ := key f
  obtain ⟨c⟩ := hn
  exact ⟨f', c, lastIdeal_and_boundary_comap_of_isAdmissible T T' g hT hT' hflat hmult hideal hbdry
    (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f)
    (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f') c⟩

private theorem projectionToBase_mem_orderAtLeastLocus (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (σ : T.SequenceOfBlowups)
    (j : ℕ) (hj : j ≤ σ.toSequenceOfBlowups.length) (z : ↥(σ.toSequenceOfBlowups.schemeAt j))
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) T.mult) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus T.ideal T.mult := by
  have hval : ∀ l ≤ σ.toSequenceOfBlowups.length, (T.transformAt σ l).IsAdmissible := by
    intro l hl
    exact hG.monomialInputs.level_valid T hT σ l hl
  have hsub := MarkedSequenceOfBlowups.orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    T σ hval T.mult le_rfl 0 j (Nat.zero_le j) hj
  have h0 : (σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z ∈ orderAtLeastLocus (σ.ideal 0) T.mult := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero T.ideal T.mult] at h0
  have hcomp : (σ.toSequenceOfBlowups.projectionToBase j).base z
      = (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z) := by
    rw [SequenceOfBlowups.projectionToBase_def]
    simp
  rw [hcomp]
  exact h0

private theorem nonempty_sequenceOfBlowupsPullback_of_center_not_mem_range {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hflat : AlgebraicGeometry.Flat g) (sD : SequenceOfBlowups X) (sU : SequenceOfBlowups Y)
    (hU : sU.length = 0)
    (hmiss : ∀ i : ℕ, i < sD.length → ∀ z : ↥(sD.schemeAt i), z ∈ (sD.center i).support →
      ∀ y : ↥Y, g.base y ≠ (sD.projectionToBase i).base z) :
    Nonempty (SequenceOfBlowupsPullback g sU sD) := by
  have := hflat
  refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq (SequenceOfBlowupsPullback.ofCentersMissImage g (BlowupSequenceData.ofSequenceOfBlowups sD) ?_
    (BlowupSequenceData.ofSequenceOfBlowups sU) ?_)⟩
  · intro i hi z hz y
    rw [BlowupSequenceData.ofSequenceOfBlowups_length sD] at hi
    have hproj : (BlowupSequenceData.ofSequenceOfBlowups sD).projectionToBase i = sD.projectionToBase i :=
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups sD) i).symm.trans
        (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups sD i)
    rw [hproj]
    exact hmiss i hi z hz y
  · exact (BlowupSequenceData.ofSequenceOfBlowups_length sU).trans hU

private theorem exists_sequenceOfBlowupsPullback_congr {T T' : MarkedIdealWithBoundary.{u}} (g : T'.scheme ⟶ T.scheme)
    (S₁ S₂ : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (R₁ R₂ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hS : S₁ = S₂) (hR : R₁ = R₂)
    (hex : ∃ c : SequenceOfBlowupsPullback g S₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups R₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S₁.ideal S₁.length = (R₁.ideal R₁.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (S₁.boundary S₁.length)
        ((R₁.boundary R₁.length).map fun D => D.comap c.lastMap)) :
    ∃ c : SequenceOfBlowupsPullback g S₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups R₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S₂.ideal S₂.length = (R₂.ideal R₂.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (S₂.boundary S₂.length)
        ((R₂.boundary R₂.length).map fun D => D.comap c.lastMap) := by
  subst hS
  subst hR
  exact hex

private theorem isLocallyMonomialTriple_tripleAtLength_congr (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν)
    (h : MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T s J μ)) :
    MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T s K ν) := by
  subst hJK
  subst hμν
  exact h

private theorem isPullbackBlowupSequence_monomialPrincipalization_congr (hinv : ComapIsoInvariance.{u})
    (T T' : MarkedIdealWithBoundary.{u})
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (f : S'.obj S'.length ⟶ S.obj S.length)
    (J : (S.obj S.length).IdealSheafData) (μ : ℕ)
    (K₁ K₂ : (S'.obj S'.length).IdealSheafData) (ν₁ ν₂ : ℕ)
    (hK : K₁ = K₂) (hν : ν₁ = ν₂)
    (h : IsPullbackBlowupSequence f (monomialPrincipalization hinv (tripleAtLength T' S' K₁ ν₁)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S J μ)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence f (monomialPrincipalization hinv (tripleAtLength T' S' K₂ ν₂)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S J μ)).toSequenceOfBlowups := by
  subst hK
  subst hν
  exact h

private theorem isPullbackSequenceOfBlowups_monomial_of_pullback (hinv : ComapIsoInvariance.{u})
    (hmg : MonomialGeometryHypotheses.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hmult : T'.mult = T.mult)
    (hidealLastComap : S'.ideal S'.length = (S.ideal S.length).comap c.lastMap)
    (hlastBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (S'.boundary S'.length)
      ((S.boundary S.length).map fun D => D.comap c.lastMap))
    (hmonLow : MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T S (S.ideal S.length) T.mult))
    (hmonUp : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T' S' (S'.ideal S'.length) T'.mult)) :
    IsPullbackBlowupSequence c.lastMap
      (monomialPrincipalization hinv (tripleAtLength T' S' (S'.ideal S'.length) T'.mult)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S (S.ideal S.length) T.mult)).toSequenceOfBlowups := by
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT S
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT S
  have hmonUp' : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T' S' ((S.ideal S.length).comap c.lastMap) T.mult) :=
    isLocallyMonomialTriple_tripleAtLength_congr T' S' (S'.ideal S'.length)
      ((S.ideal S.length).comap c.lastMap) T'.mult T.mult hidealLastComap hmult hmonUp
  have hmain := hbc.monomialBody (SequenceOfBlowupsPullback.toMarkedPullbackSquare g S S' c hdimS hvalS) hmonLow
    (S'.boundary S'.length) hlastBoundary.symm hmonUp'
  exact isPullbackBlowupSequence_monomialPrincipalization_congr hinv T T' S S' c.lastMap (S.ideal S.length)
    T.mult ((S.ideal S.length).comap c.lastMap) (S'.ideal S'.length) T.mult T'.mult hidealLastComap.symm
    hmult.symm hmain

private theorem orderReductionSeq_isPullbackBlowupSequence_of_comap (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) :
    IsPullbackBlowupSequence g (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups := by
  classical
  by_cases hemp : orderAtLeastLocus T'.ideal T'.mult = ∅
  · have hU : (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups.length = 0 :=
      orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T' A hemp
    have hmiss : ∀ i : ℕ, i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.length →
        ∀ z : ↥((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.schemeAt i),
          z ∈ ((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.center i).support →
          ∀ y : ↥T'.scheme,
            g.base y ≠ ((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.projectionToBase i).base z := by
      intro i hi z hz y hcon
      have hz' : z ∈ orderAtLeastLocus ((orderReductionSeq hinv T (principalizationOfDimLe T A)).ideal i) T.mult :=
        (orderReductionSeq hinv T (principalizationOfDimLe T A)).center_order i hi hz
      have hkey := projectionToBase_mem_orderAtLeastLocus hG hinv T hT (orderReductionSeq hinv T (principalizationOfDimLe T A)) i
        (le_of_lt hi) z hz'
      rw [← hcon] at hkey
      have hordy := orderAt_comap_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc T.ideal y
      have hmem : y ∈ orderAtLeastLocus T'.ideal T'.mult := by
        rw [mem_orderAtLeastLocus_iff, hideal, hmult, hordy]
        exact (mem_orderAtLeastLocus_iff T.ideal T.mult (g.base y)).1 hkey
      rw [hemp] at hmem
      simp only [Set.mem_empty_iff_false] at hmem
    obtain ⟨cc⟩ := nonempty_sequenceOfBlowupsPullback_of_center_not_mem_range g hbc.flat
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups
      (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups hU hmiss
    exact cc.isPullbackSequenceOfBlowups
  · have hT'ne : (orderAtLeastLocus T'.ideal T'.mult).Nonempty := Set.nonempty_iff_ne_empty.2 hemp
    have hTne : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
      rcases Set.eq_empty_or_nonempty (orderAtLeastLocus T.ideal T.mult) with h | h
      · exfalso
        apply hemp
        rw [hideal, hmult]
        exact orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc h
      · exact h
    obtain ⟨f', hc⟩ := companionIdealReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT hT'
      hdim hdim' hmult hideal hbdry hbc (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1)
    have hlowStop : ¬ CompanionIdealReductionContinues T
        (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
          (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1)) := by
      rw [← companionIdealReduction_eq hinv T (principalizationOfDimLe T A)]
      exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim
    have hupStop : ¬ CompanionIdealReductionContinues T'
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f') := by
      obtain ⟨c0, h1, h2⟩ := hc
      intro hcont
      exact hlowStop (companionIdealReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
        hideal hbdry hbc _ _ c0 h1 h2 hcont)
    have hstop' : ¬ CompanionIdealReductionContinues T'
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
          (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) + 1)) := by
      rw [← companionIdealReduction_eq hinv T' (principalizationOfDimLe T' A)]
      exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT' hdim'
    have hupEq : companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f'
        = companionIdealReduction hinv T' (principalizationOfDimLe T' A) := by
      rw [companionIdealReduction_eq hinv T' (principalizationOfDimLe T' A)]
      rcases le_total f' (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) + 1) with h | h
      · exact (companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
          (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f' hupStop _ h).symm
      · exact companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
          (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) _ hstop' f' h
    obtain ⟨c, hidealLastComap, hlastBoundary⟩ := exists_sequenceOfBlowupsPullback_congr g _ _ _ _ hupEq
      (companionIdealReduction_eq hinv T (principalizationOfDimLe T A)).symm hc
    have hmonLow : MonomialCenter.IsLocallyMonomialTriple
        (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
          ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) :=
      isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
    have hmonUp : MonomialCenter.IsLocallyMonomialTriple
        (tripleAtLength T' (companionIdealReduction hinv T' (principalizationOfDimLe T' A))
          ((companionIdealReduction hinv T' (principalizationOfDimLe T' A)).ideal
            (companionIdealReduction hinv T' (principalizationOfDimLe T' A)).length) T'.mult) :=
      isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT' hdim'
    have hIP := isPullbackSequenceOfBlowups_monomial_of_pullback hinv hG.monomialInputs n A
      T T' g hT hbc (companionIdealReduction hinv T (principalizationOfDimLe T A)) (companionIdealReduction hinv T' (principalizationOfDimLe T' A)) c hmult
      hidealLastComap hlastBoundary hmonLow hmonUp
    obtain ⟨cc⟩ := hIP.nonempty_sequenceOfBlowupsPullback
    rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hTne, orderReductionSeq_eq_of_nonempty hinv T' (principalizationOfDimLe T' A) hT'ne,
      orderReductionData_eq_append hinv T A, orderReductionData_eq_append hinv T' A]
    exact isPullbackBlowupSequence_append_of_two_fields g (companionIdealReduction hinv T (principalizationOfDimLe T A)) (orderReductionMonomialSequence hinv T A)
      (companionIdealReduction hinv T' (principalizationOfDimLe T' A)) (orderReductionMonomialSequence hinv T' A) hinv c
      (SequenceOfBlowupsPullback.toBlowupDataOfSeq cc)

theorem orderReductionSeq_isPullbackBlowupSequence_mk (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    {Y : Scheme.{u}} (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').IsAdmissible)
    (hdim' : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').krullDimSucc ≤ n)
    (hbc : BaseChangeCompatible hinv A n T g k' q) :
    IsPullbackBlowupSequence g
      (orderReductionSeq hinv (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E')
        (principalizationOfDimLe (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E') A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups :=
  orderReductionSeq_isPullbackBlowupSequence_of_comap hG hinv n A B hspec T
    (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E') g hT hT' hdim hdim' rfl rfl hE hbc

theorem orderReductionSeq_isPullbackBlowupSequence_pullbackOverField (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    {Y : Scheme.{u}} (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : ((T.pullbackOverField Y k' q g).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackOverField Y k' q g).withBoundary E').krullDimSucc ≤ n)
    (hbc : BaseChangeCompatible hinv A n T g k' q) :
    IsPullbackBlowupSequence g
      (orderReductionSeq hinv ((T.pullbackOverField Y k' q g).withBoundary E')
        (principalizationOfDimLe ((T.pullbackOverField Y k' q g).withBoundary E') A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups := by
  have hT2 : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').IsAdmissible := hT'
  have hdim2 : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').krullDimSucc ≤ n := hdim'
  exact orderReductionSeq_isPullbackBlowupSequence_mk hG hinv n A B hspec T hT hdim k' q g E' hE hT2 hdim2 hbc

end FunctorialResolution.EmbeddedResolution

end
