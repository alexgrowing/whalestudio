import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q g).boundary.length :=
  pullbackOverFieldIndex T Y k' q g

@[simp]
theorem pullbackIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackIndex T Y k' q g j : Fin (T.pullbackOverField Y k' q g).boundary.length) : ℕ) = (j : ℕ) :=
  pullbackOverFieldIndex_val T Y k' q g j

def pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin (T.pullbackOverField Y k' q g).boundary.length → Fin T.boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g)

@[simp]
theorem pullbackIndexSymm_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    ((pullbackIndexSymm T Y k' q g j : Fin T.boundary.length) : ℕ) = (j : ℕ) :=
  rfl

@[simp]
theorem pullbackIndexSymm_pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    pullbackIndexSymm T Y k' q g (pullbackIndex T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndexSymm_val, pullbackIndex_val]

@[simp]
theorem pullbackIndex_pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    pullbackIndex T Y k' q g (pullbackIndexSymm T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndex_val, pullbackIndexSymm_val]

def pullbackAlongIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackAlong Y q g).boundary.length :=
  EmbeddedResolution.pullbackAlongIndex T Y q g

@[simp]
theorem pullbackAlongIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q g j : Fin (T.pullbackAlong Y q g).boundary.length) : ℕ) = (j : ℕ) :=
  EmbeddedResolution.pullbackAlongIndex_val T Y q g j

structure IsComponentCompatiblePullback (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) : Prop where
  comapCenter : ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
    𝒞 ⊆ intersectionComponents T.boundary J →
    ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (Finset.image (pullbackIndex T Y k' q g) J)).subschemeι ⁻¹'
          ⋃₀ {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
        (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
          componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) J)
            {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  componentsDown : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
      ∃ C ∈ intersectionComponents T.boundary J, Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  componentsUp : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C ∈ intersectionComponents T.boundary J, ∀ y : ↥Y, g y ∈ C →
      ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
        y ∈ C' ∧
          ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  orderAtComap : ∀ (I : T.scheme.IdealSheafData) (y : ↥Y), orderAt (I.comap g) y = orderAt I (g y)

theorem centerInvariant_le_iff {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (I' : Y'.IdealSheafData) (m' : ℕ) (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Le (centerInvariant I' m' L') ↔
      ((centerInvariant I m L).Lt (centerInvariant I' m' L') ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧ maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
          sortedIndices (lexMaxIndices I m L) = sortedIndices (lexMaxIndices I' m' L'))) :=
  Iff.rfl

theorem minIndexCard_ne_zero_and_le_pullbackOverField (_hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (_hT : IsLocallyMonomialTriple T)
    (_hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      minIndexCard T.ideal T.mult T.boundary ≤
        minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary := by
  obtain ⟨J', C', hcard', hmem', hord'⟩ :=
    exists_isCandidateComponent_minIndexCard (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary h0
  have hinj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg (fun z : Fin T.boundary.length => (z : ℕ)) hab
    simpa using h
  have hJ : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rwa [pullbackIndex_pullbackIndexSymm]
    · intro hx
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g x,
        Finset.mem_image.2 ⟨x, hx, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g x⟩
  obtain ⟨C, hC, -, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C'
      (by rw [hJ]; exact hmem')
  have h4 : g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmem')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have heq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    have e1 : orderAlong (T.pullbackOverField Y k' q g).ideal C'
        = orderAt (T.pullbackOverField Y k' q g).ideal
            (isIrreducible_of_mem_intersectionComponents hmem').genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hmem'
    have e2 : orderAt (T.pullbackOverField Y k' q g).ideal
          (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
        = orderAt T.ideal (g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint) :=
      hP.orderAtComap T.ideal _
    have e3 : orderAlong T.ideal C
        = orderAt T.ideal (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hC
    rw [e1, e2, h4, e3]
  have hord2 : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hx : (T.mult : ℕ∞) ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := hord'
    rw [heq] at hx
    exact hx
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card = J'.card :=
    Finset.card_image_of_injective J' hinj
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    ⟨hcardJ.trans hcard', hC, hord2⟩
  have hone : 1 ≤ minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary := Nat.pos_of_ne_zero h0
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary, hone,
      Finset.image (pullbackIndexSymm T Y k' q g) J', C, hcand⟩
  have hspec := minIndexCard_spec T.ideal T.mult T.boundary hex
  refine ⟨?_, hspec.2.2 _ hone _ _ hcand⟩
  have h1 := hspec.1
  omega

theorem maxCandidateOrder_le_of_minIndexCard_eq (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by
    rw [hmin]
    exact h0
  obtain ⟨J', C', hcand', hord'⟩ := (maxCandidateOrder_spec hGeom hT' h0').1
  have hcandSplit :
      J'.card = minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary ∧
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary J' ∧
        ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
          orderAlong (T.pullbackOverField Y k' q g).ideal C' := hcand'
  obtain ⟨hcard', hmemC', hmult'⟩ := hcandSplit
  have hback_inj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg Fin.val hab
    rwa [pullbackIndexSymm_val, pullbackIndexSymm_val] at h
  have himg : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rw [pullbackIndex_pullbackIndexSymm]
      exact hb
    · intro hj
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g j⟩
  have hmem : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (Finset.image (pullbackIndexSymm T Y k' q g) J')) := by
    rw [himg]
    exact hmemC'
  obtain ⟨C, hC, _hmaps, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C' hmem
  have hg : g (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint =
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmemC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    rw [orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hmemC',
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, ← hg]
    exact hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hback_inj, hcard']
    exact hmin
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hb := hmult'
    rw [hord] at hb
    exact hb
  have hcandT : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    And.intro hcardJ (And.intro hC hmultC)
  have hmaxOrd := (maxCandidateOrder_spec hGeom hT h0).2.1 _ _ hcandT
  rw [← hord', hord]
  exact hmaxOrd

private theorem centerInvariant_lt_iff_lex {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (I' : Y'.IdealSheafData) (m' : ℕ)
    (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Lt (centerInvariant I' m' L') ↔
      (minIndexCard I m L < minIndexCard I' m' L' ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧
          (maxCandidateOrder I' m' L' < maxCandidateOrder I m L ∨
            (maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
              List.Lex (· < ·) (sortedIndices (lexMaxIndices I m L))
                (sortedIndices (lexMaxIndices I' m' L')))))) :=
  Iff.rfl

private theorem pullbackIndexSymm_injective (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Function.Injective (pullbackIndexSymm T Y k' q g) := by
  intro a b h
  apply Fin.val_injective
  rw [← pullbackIndexSymm_val T Y k' q g a, ← pullbackIndexSymm_val T Y k' q g b, h]

private theorem pullbackIndex_strictMono (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    StrictMono (pullbackIndex T Y k' q g) := by
  intro a b hab
  have h : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hab
  rw [Fin.lt_def, pullbackIndex_val, pullbackIndex_val]
  exact h

private theorem sortedIndices_image_pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) :
    sortedIndices (Finset.image (pullbackIndex T Y k' q g) J) = sortedIndices J := by
  rw [sortedIndices_image_of_strictMono (pullbackIndex T Y k' q g)
    (pullbackIndex_strictMono T Y k' q g) J]
  simp only [pullbackIndex_val]
  rfl

private theorem orderAlong_pullbackOverField_eq_orderAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (hP : IsComponentCompatiblePullback T Y k' q g) (J : Finset (Fin T.boundary.length))
    (C' : Set ↥Y) (C : Set ↥T.scheme)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) J))
    (hC : C ∈ intersectionComponents T.boundary J)
    (hgen : ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ) :
    orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
  have h1 := orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hC'
  have h2 := orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC
  have hg := hgen (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have h3 := hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hC').genericPoint
  exact h1.trans (h3.trans ((congrArg (orderAt T.ideal) hg).trans h2.symm))

theorem minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g) :
    minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 ∨
      (centerInvariant T.ideal T.mult T.boundary).Le
        (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) := by
  by_cases h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary = 0
  · exact Or.inl h0'
  refine Or.inr ?_
  obtain ⟨h0, hle⟩ := minIndexCard_ne_zero_and_le_pullbackOverField hGeom T Y k' q g hT hT' hP h0'
  rw [centerInvariant_le_iff, centerInvariant_lt_iff_lex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (Or.inl hlt)
  have hmaxle := maxCandidateOrder_le_of_minIndexCard_eq hGeom T Y k' q g hT hT' hP heq.symm h0
  rcases lt_or_eq_of_le hmaxle with hmlt | hmeq
  · exact Or.inl (Or.inr ⟨heq, Or.inl hmlt⟩)
  have hoptT := lexMaxIndices_spec hGeom hT h0
  have hoptT' := lexMaxIndices_spec hGeom hT' h0'
  have hbest' : ∃ C : Set ↥Y,
      IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary
        (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary)
        (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) C ∧
        orderAlong (T.pullbackOverField Y k' q g).ideal C =
          maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary := And.left hoptT'
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hmemC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary) := And.left (And.right hcand')
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
      orderAlong (T.pullbackOverField Y k' q g).ideal C' := And.right (And.right hcand')
  have hex : ∃ B : Finset (Fin T.boundary.length),
      Finset.image (pullbackIndex T Y k' q g) B =
          lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary ∧
        B.card = (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary).card := by
    refine ⟨Finset.image (pullbackIndexSymm T Y k' q g)
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary), ?_, ?_⟩
    · rw [Finset.image_image]
      have hcomp : (pullbackIndex T Y k' q g) ∘ (pullbackIndexSymm T Y k' q g) = id :=
        funext (pullbackIndex_pullbackIndexSymm T Y k' q g)
      rw [hcomp, Finset.image_id]
    · exact Finset.card_image_of_injective _ (pullbackIndexSymm_injective T Y k' q g)
  obtain ⟨B, hBim, hBcard⟩ := hex
  have hmemB : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) B) := by
    rw [hBim]
    exact hmemC'
  obtain ⟨C, hC, -, hgenericPt⟩ := hP.componentsDown B C' hmemB
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP B C' C hmemB hC hgenericPt
  have hcardB : B.card = minIndexCard T.ideal T.mult T.boundary := by
    rw [hBcard, card_lexMaxIndices hGeom hT' h0']
    exact heq.symm
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [← hordEq]
    exact hmultC'
  have hmaxC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [← hordEq, hordC']
    exact hmeq
  have hbestB : IsMaxOrderIndexSet T.ideal T.mult T.boundary B :=
    Exists.intro C (And.intro (And.intro hcardB (And.intro hC hmultC)) hmaxC)
  have hnotlex := And.right hoptT B hbestB
  have hsp : sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) =
      sortedIndices B := by
    rw [← hBim]
    exact sortedIndices_image_pullbackIndex T Y k' q g B
  rcases trichotomous_of (List.Lex (· < ·))
      (sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
      (sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) with
    hlex | hlexeq | hlex
  · exact Or.inl (Or.inr ⟨heq, Or.inr ⟨hmeq.symm, hlex⟩⟩)
  · exact Or.inr ⟨heq, hmeq.symm, hlexeq⟩
  · rw [hsp] at hlex
    exact absurd hlex hnotlex

theorem lexMaxIndices_pullbackOverField_eq_image (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (h : sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) =
      sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) :
    lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary) := by
  apply Finset.ext
  intro j'
  constructor
  · intro hj'
    have hmem : ((j' : ℕ)) ∈ sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) :=
      (mem_sortedIndices _ _).2 ⟨j', hj', rfl⟩
    rw [← h] at hmem
    obtain ⟨j, hj, hval⟩ := (mem_sortedIndices _ _).1 hmem
    refine Finset.mem_image.2 ⟨j, hj, ?_⟩
    apply Fin.val_injective
    rw [pullbackIndex_val]
    exact hval
  · intro hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    have hmem : ((j : ℕ)) ∈ sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) :=
      (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [h] at hmem
    obtain ⟨j2, hj2, hval⟩ := (mem_sortedIndices _ _).1 hmem
    have hj2eq : j2 = pullbackIndex T Y k' q g j := by
      apply Fin.val_injective
      rw [pullbackIndex_val]
      exact hval
    rwa [hj2eq] at hj2

private theorem componentUnionIdeal_congr {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J J' : Finset (Fin L.length)) (𝒞 𝒞' : Set (Set ↥Y)) (hJ : J = J') (h𝒞 : 𝒞 = 𝒞')
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞))
    (hop' : IsOpen (⇑(intersectionIdeal L J').subschemeι ⁻¹' ⋃₀ 𝒞')) :
    componentUnionIdeal L J 𝒞 hop = componentUnionIdeal L J' 𝒞' hop' := by
  subst hJ
  subst h𝒞
  rfl

theorem monomialCenter_pullbackOverField_eq_comap (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (hmax : maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = maxCandidateOrder T.ideal T.mult T.boundary)
    (hch : lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :
    monomialCenter (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      (monomialCenter T.ideal T.mult T.boundary).comap g := by
  by_cases h0 : minIndexCard T.ideal T.mult T.boundary = 0
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 := by rw [hmin]; exact h0
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0']
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0]
    exact (Scheme.IdealSheafData.comap_top g).symm
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0 := by rw [hmin]; exact h0
    obtain ⟨hop', heq⟩ := hP.comapCenter (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)
    have hSet : centerComponents (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary =
        {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) ∧
          ∃ C ∈ centerComponents T.ideal T.mult T.boundary, Set.MapsTo (⇑g) C' C} := by
      ext C'
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hmem
        obtain ⟨hcand, hordC'⟩ := (mem_centerComponents_iff _ _ _ C').1 hmem
        obtain ⟨hcardJ', hmemC', hmultC'⟩ := hcand
        rw [hch] at hmemC'
        refine ⟨hmemC', ?_⟩
        obtain ⟨C, hC, hmaps, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C hmemC' hC hgen
        refine ⟨C, (mem_centerComponents_iff _ _ _ C).2
          ⟨⟨card_lexMaxIndices hGeom hT h0, hC, ?_⟩, ?_⟩, hmaps⟩
        · rw [← hord]
          exact hmultC'
        · rw [← hord, hordC']
          exact hmax
      · rintro ⟨hmemC', C, hCopt, hmaps⟩
        obtain ⟨hcandC, hordC⟩ := (mem_centerComponents_iff _ _ _ C).1 hCopt
        obtain ⟨hcardJ, hCmem, hmultC⟩ := hcandC
        obtain ⟨C₀, hC₀, hmaps₀, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hmemC').nonempty
        have hCC₀ : C₀ = C := by
          by_contra hne
          exact Set.disjoint_left.1
            (hGeom.components_disjoint T hT.valid _ C₀ hC₀ C hCmem hne) (hmaps₀ hx) (hmaps hx)
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C₀ :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C₀ hmemC' hC₀ hgen
        refine (mem_centerComponents_iff _ _ _ C').2
          ⟨⟨card_lexMaxIndices hGeom hT' h0', ?_, ?_⟩, ?_⟩
        · rw [hch]
          exact hmemC'
        · rw [hord, hCC₀]
          exact hmultC
        · rw [hord, hCC₀, hordC]
          exact hmax.symm
    rw [monomialCenter_eq_componentUnionIdeal hGeom hT' h0',
      monomialCenter_eq_componentUnionIdeal hGeom hT h0, heq]
    exact componentUnionIdeal_congr _ _ _ _ _ hch hSet _ _

theorem comap_monomialCenter_eq_top (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hkey : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary = 0 ∨
        (centerInvariant T.ideal T.mult T.boundary).Lt
          (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary)) :
    (monomialCenter T.ideal T.mult T.boundary).comap g = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support g (monomialCenter T.ideal T.mult T.boundary) ?_
  intro y hy
  have hmem : g y ∈ monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h0]
    exact hy
  rw [monomialCenterSet_eq_sUnion_centerComponents, Set.mem_sUnion] at hmem
  obtain ⟨C, hCopt, hgyC⟩ := hmem
  obtain ⟨hcandC, hordC⟩ :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hCopt
  obtain ⟨-, hmemC, hmultC⟩ := hcandC
  obtain ⟨C', hC'mem, -, hgen⟩ :=
    hP.componentsUp (lexMaxIndices T.ideal T.mult T.boundary) C hmemC y hgyC
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
      (lexMaxIndices T.ideal T.mult T.boundary) C' C hC'mem hmemC hgen
  have hinj : Function.Injective (pullbackIndex T Y k' q g) :=
    (pullbackIndex_strictMono T Y k' q g).injective
  have hcard' : (Finset.image (pullbackIndex T Y k' q g)
      (lexMaxIndices T.ideal T.mult T.boundary)).card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hinj]
    exact card_lexMaxIndices hGeom hT h0
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞)
      ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := by
    rw [hordEq]
    exact hmultC
  have hcand' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' :=
    ⟨hcard', hC'mem, hmultC'⟩
  have hone : 1 ≤ minIndexCard T.ideal T.mult T.boundary := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      ⟨minIndexCard T.ideal T.mult T.boundary, hone,
        Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary), C',
        hcand'⟩
  have hle : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≤ minIndexCard T.ideal T.mult T.boundary :=
    hspec.2.2 _ hone _ _ hcand'
  have hgeone := hspec.1
  rcases hkey with hzero | hlt
  · omega
  rw [centerInvariant_lt_iff_lex] at hlt
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by omega
  rcases hlt with hml | ⟨hmeq, hrest⟩
  · omega
  have hcand'' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' := by
    rw [← hmeq]
    exact hcand'
  have hordC' : orderAlong (T.pullbackOverField Y k' q g).ideal C'
      = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [hordEq]
    exact hordC
  rcases hrest with hmax | ⟨hmaxeq, hlex⟩
  · have hb := (maxCandidateOrder_spec hGeom hT' h0').2.1 _ _ hcand''
    rw [hordC'] at hb
    exact absurd hmax (not_lt.mpr hb)
  have hbest : IsMaxOrderIndexSet (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :=
    ⟨C', hcand'', hordC'.trans hmaxeq⟩
  have hnot := (lexMaxIndices_spec hGeom hT' h0').2 _ hbest
  rw [sortedIndices_image_pullbackIndex T Y k' q g (lexMaxIndices T.ideal T.mult T.boundary)] at hnot
  exact hnot hlex

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
