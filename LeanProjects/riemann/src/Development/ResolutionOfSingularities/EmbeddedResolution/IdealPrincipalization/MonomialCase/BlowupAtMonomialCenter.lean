import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def blowupTriple (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := inferInstance
  scheme := X'
  structMap := q
  ideal := I'
  mult := T.mult
  boundary := transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary

theorem blowupTriple_baseField (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').base = T.base := rfl

@[simp] theorem blowupTriple_scheme (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').scheme = X' := rfl

theorem blowupTriple_structureMorphism (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').structMap = q := rfl

@[simp] theorem blowupTriple_ideal (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').ideal = I' := rfl

@[simp] theorem blowupTriple_mult (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').mult = T.mult := rfl

@[simp] theorem blowupTriple_boundary (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').boundary =
      transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary := rfl

theorem orderAt_transform_eq_of_not_mem_exceptional (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    (x' : ↥X')
    (hx' : x' ∉ (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support) :
    orderAt I' x' = orderAt T.ideal (π x') := by
  have hE : Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)
      = (monomialCenter T.ideal T.mult T.boundary).comap π := by
    rw [Blowup.exceptionalIdeal_eq_comap]
  have hx2 : x' ∉ ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    rw [← hE]
    exact hx'
  have htop : stalkIdeal ((monomialCenter T.ideal T.mult T.boundary).comap π) x' = ⊤ := by
    by_contra hne
    exact hx2 ((mem_support_iff_stalkIdeal_ne_top _ _).2 hne)
  have hst : stalkIdeal (T.ideal.comap π) x' = stalkIdeal I' x' := by
    rw [← hI', stalkIdeal_mul, stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow, one_mul]
  exact (orderAt_eq_of_stalkIdeal_eq hst).symm.trans
    (hGeom.orderAt_comap_off_exceptional T hT.valid X' π
      (monomialCenter T.ideal T.mult T.boundary) hπ x' hx' T.ideal)

theorem orderAlong_transform_eq_of_genericPoint_not_mem_exceptional (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (_h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    {J : Finset (Fin T.boundary.length)} {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      (J.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)))
    (hoff : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∉
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support) :
    orderAlong I' C' = orderAlong T.ideal (⇑π '' C') := by
  have hgen : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC').genericPoint C' :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC'
  have hSirr : IsIrreducible (⇑π '' C') :=
    (isIrreducible_of_mem_intersectionComponents hC').image _ π.continuous.continuousOn
  have hclim : closure (⇑π '' C')
      = closure ({π (isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥T.scheme) :=
    closure_image_genericPoint (f := ⇑π) π.continuous hgen
  have h2 : orderAlong T.ideal (⇑π '' C')
      = orderAt T.ideal (π (isIrreducible_of_mem_intersectionComponents hC').genericPoint) := by
    rw [orderAlong_eq_orderAt_genericPoint T.ideal hSirr]
    have h3 : closure ({hSirr.genericPoint} : Set ↥T.scheme)
        = closure ({π (isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥T.scheme) := by
      rw [← hclim]
      simp
    rw [(inseparable_iff_closure_eq.mpr h3).eq]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', h2]
  exact orderAt_transform_eq_of_not_mem_exceptional hGeom hT π hπ I' hI' _ hoff

private theorem get_transformedBoundary_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  have hlt : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ)
      < (L.map (Blowup.strictTransform π Z)).length := by
    rw [strictTransformIndex_val]
    simp
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left hlt]
  exact List.getElem_map _

private theorem get_transformedBoundary_exceptionalIndex {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) :
    (transformedBoundary π Z L).get (exceptionalIndex π Z L) = Blowup.exceptionalIdeal π Z := by
  have hge : (L.map (Blowup.strictTransform π Z)).length
      ≤ ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) := by
    rw [exceptionalIndex_val]
    simp
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right hge]
  simp [exceptionalIndex_val]

private theorem strictTransformIndex_injective {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : Function.Injective (strictTransformIndex π Z L) := by
  intro i j hij
  have hv : ((strictTransformIndex π Z L i : Fin (transformedBoundary π Z L).length) : ℕ)
      = ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) := by rw [hij]
  rw [strictTransformIndex_val, strictTransformIndex_val] at hv
  exact Fin.val_injective hv

private theorem eq_exceptionalIndex_or_exists_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (i : Fin (transformedBoundary π Z L).length) :
    i = exceptionalIndex π Z L ∨ ∃ j : Fin L.length, strictTransformIndex π Z L j = i := by
  have hlen := transformedBoundary_length π Z L
  have hi : (i : ℕ) < (transformedBoundary π Z L).length := i.isLt
  have hlt : (i : ℕ) < L.length + 1 := by omega
  rcases Nat.lt_or_ge (i : ℕ) L.length with hj | hj
  · exact Or.inr ⟨⟨(i : ℕ), hj⟩, Fin.val_injective (by rw [strictTransformIndex_val])⟩
  · refine Or.inl (Fin.val_injective ?_)
    rw [exceptionalIndex_val]
    omega

private theorem image_strictTransformIndex_preimageStrictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length))
    (hnew : exceptionalIndex π Z L ∉ J') :
    (preimageStrictTransformIndex π Z L J').image (strictTransformIndex π Z L) = J' := by
  classical
  ext i
  simp only [Finset.mem_image, mem_preimageStrictTransformIndex_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    rcases eq_exceptionalIndex_or_exists_strictTransformIndex π Z L i with rfl | ⟨j, rfl⟩
    · exact absurd hi hnew
    · exact ⟨j, hi, rfl⟩

private theorem card_preimageStrictTransformIndex_of_not_mem {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) (hnew : exceptionalIndex π Z L ∉ J') :
    (preimageStrictTransformIndex π Z L J').card = J'.card := by
  classical
  have h1 := Finset.card_image_of_injective (preimageStrictTransformIndex π Z L J') (strictTransformIndex_injective π Z L)
  rw [image_strictTransformIndex_preimageStrictTransformIndex π Z L J' hnew] at h1
  exact h1.symm

private theorem card_preimageStrictTransformIndex_add_one_of_mem {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) (hnew : exceptionalIndex π Z L ∈ J') :
    (preimageStrictTransformIndex π Z L J').card + 1 = J'.card := by
  classical
  have himg : (preimageStrictTransformIndex π Z L J').image (strictTransformIndex π Z L) = J'.erase (exceptionalIndex π Z L) := by
    ext i
    simp only [Finset.mem_image, mem_preimageStrictTransformIndex_iff, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, hj⟩
      intro hc
      have hval : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ)
          = ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) := by rw [hc]
      rw [strictTransformIndex_val, exceptionalIndex_val] at hval
      exact absurd hval (Nat.ne_of_lt j.isLt)
    · rintro ⟨hne, hi⟩
      rcases eq_exceptionalIndex_or_exists_strictTransformIndex π Z L i with rfl | ⟨j, rfl⟩
      · exact absurd rfl hne
      · exact ⟨j, hi, rfl⟩
  have h1 := Finset.card_image_of_injective (preimageStrictTransformIndex π Z L J') (strictTransformIndex_injective π Z L)
  rw [himg, Finset.card_erase_of_mem hnew] at h1
  have h2 : 1 ≤ J'.card := Finset.card_pos.2 ⟨_, hnew⟩
  omega

private theorem exists_orderAt_comap_eq_strictTransform_add_exceptional (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hq : AlgebraicGeometry.Smooth q)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (i : Fin T.boundary.length) (x' : ↥X') :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧
      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
        ((↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ∩
            (V : Set ↥T.scheme)) ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme)) ∧
      orderAt ((T.boundary.get i).comap π) x'
        = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) x'
          + (ε : ℕ∞) *
            orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth q := hq
  have hmemL : T.boundary.get i ∈ T.boundary := by simp
  obtain ⟨U', ε, hx'U', hε01, hεiff, hfact⟩ :=
    hGeom.blowup_total_transform T hT.valid (monomialCenter T.ideal T.mult T.boundary)
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) X' π hπ
      (T.boundary.get i) hmemL x'
  refine ⟨ε, hε01, hεiff, ?_⟩
  have : AlgebraicGeometry.Smooth U'.ι := inferInstance
  have : AlgebraicGeometry.Smooth (U'.ι ≫ q) := inferInstance
  have e1 : orderAt (((T.boundary.get i).comap π).comap U'.ι) ⟨x', hx'U'⟩
      = orderAt ((T.boundary.get i).comap π) x' :=
    orderAt_comap T.base q U'.ι ((T.boundary.get i).comap π) ⟨x', hx'U'⟩
  have e2 : orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i)).comap U'.ι) ⟨x', hx'U'⟩
      = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
          (T.boundary.get i)) x' :=
    orderAt_comap T.base q U'.ι
      (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary) (T.boundary.get i))
      ⟨x', hx'U'⟩
  have e3 : orderAt ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
        ⟨x', hx'U'⟩
      = orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' :=
    orderAt_comap T.base q U'.ι
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) ⟨x', hx'U'⟩
  have hmul := orderAt_mul T.base (U'.ι ≫ q)
      ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i)).comap U'.ι)
      (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ^ ε)
      ⟨x', hx'U'⟩
  have hpow := orderAt_pow T.base (U'.ι ≫ q)
      ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ε
      ⟨x', hx'U'⟩
  have h4 : orderAt (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
        ^ ε) ⟨x', hx'U'⟩
      = (ε : ℕ∞) *
        orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' :=
    hpow.trans (congrArg (fun z : ℕ∞ => (ε : ℕ∞) * z) e3)
  calc orderAt ((T.boundary.get i).comap π) x'
      = orderAt (((T.boundary.get i).comap π).comap U'.ι) ⟨x', hx'U'⟩ := e1.symm
    _ = orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)).comap U'.ι *
          ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ^ ε)
          ⟨x', hx'U'⟩ := by rw [hfact]
    _ = orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)).comap U'.ι) ⟨x', hx'U'⟩
        + orderAt (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
            ^ ε) ⟨x', hx'U'⟩ := hmul
    _ = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) x'
        + (ε : ℕ∞) *
          orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' := by
        rw [e2, h4]

private theorem comap_foldr_mul {X Y : Scheme.{u}} (f : Y ⟶ X) (l : List X.IdealSheafData) :
    (l.foldr (· * ·) ⊤).comap f = (l.map (fun A => A.comap f)).foldr (· * ·) ⊤ := by
  induction l with
  | nil => simp
  | cons A l ih =>
    simp only [List.foldr_cons, List.map_cons,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]

theorem orderAlong_transform_add_mult_of_exceptionalIndex_mem (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    {J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length)}
    (hJ' : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J')
    {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) J')
    (U : T.scheme.Opens)
    (hU : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ U)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    {C₀ : Set ↥T.scheme}
    (hC₀ : C₀ ∈ centerComponents T.ideal T.mult T.boundary)
    (hmem₀ : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ C₀) :
    orderAlong I' C' + (T.mult : ℕ∞) =
      ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i : ℕ) : ℕ∞)
        + orderAlong T.ideal C₀ := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth q := hT'.valid.smooth
  have hC'' : C' ∈ intersectionComponents (blowupTriple T π q I').boundary J' := hC'
  have hmemiff : ∀ i : Fin (transformedBoundary π
      (monomialCenter T.ideal T.mult T.boundary) T.boundary).length,
      ((isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        ((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC'' i
  have hEmem : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support := by
    have hx := (hmemiff (exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).2 hJ'
    rwa [get_transformedBoundary_exceptionalIndex] at hx
  have hstrictmem0 : Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)
      ∈ (blowupTriple T π q I').boundary := by
    simp only [blowupTriple_boundary]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hEord : orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary))
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 :=
    hGeom.orderAt_boundary_eq_one (blowupTriple T π q I') hT'.valid
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) hstrictmem0
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint hEmem
  have hZord : orderAt ((monomialCenter T.ideal T.mult T.boundary).comap π)
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 := by
    rw [← Blowup.exceptionalIdeal_eq_comap]
    exact hEord
  have h3 : orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = (T.mult : ℕ∞) + orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    rw [← hI', orderAt_mul T.base q, orderAt_pow T.base q, hZord, mul_one]
  have hmaxIdx : ∀ i ∈ lexMaxIndices T.ideal T.mult T.boundary,
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme)
        ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) := by
    intro i hi
    rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
    rintro y ⟨C, hCmem, hyC⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hCmem) i).2 hi hyC
  have hkeyc : ∀ (i : Fin T.boundary.length) (V : T.scheme.Opens),
      π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ V →
      ((↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme)
          ∩ (V : Set ↥T.scheme)) ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) →
      i ∈ lexMaxIndices T.ideal T.mult T.boundary := by
    intro i V hVmem hVsub
    have hC₀comp : C₀ ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
      centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC₀
    have hirr0 : IsIrreducible C₀ := isIrreducible_of_mem_intersectionComponents hC₀comp
    have hC₀Z : C₀ ⊆ (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := by
      rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
      intro y hy
      exact ⟨C₀, hC₀, hy⟩
    have hclosed : IsClosed (↑(T.boundary.get i).support : Set ↥T.scheme) :=
      (T.boundary.get i).support.2
    have hcl : closure (C₀ ∩ (V : Set ↥T.scheme))
        ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) :=
      closure_minimal (fun z hz => hVsub ⟨hC₀Z hz.1, hz.2⟩) hclosed
    have hsub2 : C₀ ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) := by
      intro y hy
      refine hcl ?_
      rw [mem_closure_iff]
      intro W hW hyW
      obtain ⟨z, hzC, hzW, hzV⟩ :=
        hirr0.2 W (V : Set ↥T.scheme) hW V.isOpen ⟨y, hy, hyW⟩
          ⟨π (isIrreducible_of_mem_intersectionComponents hC').genericPoint, hmem₀, hVmem⟩
      exact ⟨z, hzW, hzC, hzV⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC₀comp i).1 hsub2
  have hξU : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ π ⁻¹ᵁ U := hU
  have hrestr : ∀ A : T.scheme.IdealSheafData,
      (A.comap U.ι).comap (π ∣_ U) = (A.comap π).comap (π ⁻¹ᵁ U).ι := by
    intro A
    have h1 : A.comap ((π ∣_ U) ≫ U.ι) = A.comap ((π ⁻¹ᵁ U).ι ≫ π) := by
      rw [morphismRestrict_ι]
    simpa only [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp] using h1
  have hmon' : (T.ideal.comap π).comap (π ⁻¹ᵁ U).ι
      = (List.ofFn fun i : Fin T.boundary.length =>
          ((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i).foldr (· * ·) ⊤ := by
    rw [← hrestr T.ideal, hmon, comap_foldr_mul]
    congr 1
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Function.comp_apply]
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow, hrestr]
  have : AlgebraicGeometry.Smooth (π ⁻¹ᵁ U).ι := inferInstance
  have : AlgebraicGeometry.Smooth ((π ⁻¹ᵁ U).ι ≫ q) := inferInstance
  have e0 : orderAt ((T.ideal.comap π).comap (π ⁻¹ᵁ U).ι)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
      = orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint :=
    orderAt_comap T.base q (π ⁻¹ᵁ U).ι (T.ideal.comap π)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
  have ecomap : ∀ i : Fin T.boundary.length,
      orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι)
          ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
        = orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint :=
    fun i => orderAt_comap T.base q (π ⁻¹ᵁ U).ι ((T.boundary.get i).comap π)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
  have e2 : orderAt ((T.ideal.comap π).comap (π ⁻¹ᵁ U).ι)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
      = ∑ i : Fin T.boundary.length,
          orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i)
            ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩ := by
    rw [hmon', orderAt_foldr_mul T.base ((π ⁻¹ᵁ U).ι ≫ q)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩]
    simp [List.map_ofFn, List.sum_ofFn]
  have e3 : ∀ i : Fin T.boundary.length,
      orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i)
          ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
        = (a i : ℕ∞) * orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    intro i
    have hp := orderAt_pow T.base ((π ⁻¹ᵁ U).ι ≫ q)
      (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι) (a i)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
    exact hp.trans (congrArg (fun z : ℕ∞ => (a i : ℕ∞) * z) (ecomap i))
  have h1 : orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ∑ i : Fin T.boundary.length, (a i : ℕ∞) *
          orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    rw [← e0, e2]
    exact Finset.sum_congr rfl fun i _ => e3 i
  have hoi : ∀ i : Fin T.boundary.length,
      orderAt ((T.boundary.get i).comap π)
          (isIrreducible_of_mem_intersectionComponents hC').genericPoint
        = (((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) : ℕ) : ℕ∞) := by
    intro i
    obtain ⟨ε, hε01, hεiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional hGeom hT h π q hT'.valid.smooth hπ i
        (isIrreducible_of_mem_intersectionComponents hC').genericPoint
    have hstrictmem : Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i) ∈ (blowupTriple T π q I').boundary := by
      simp only [blowupTriple_boundary]
      exact List.mem_append_left _
        (List.mem_map_of_mem
          (f := Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)) (by simp))
    have hstrict : orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
          (T.boundary.get i)) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
        = ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
            then 1 else 0 : ℕ) : ℕ∞) := by
      by_cases hi : strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
      · have hmem := (hmemiff
          (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i)).2 hi
        rw [get_transformedBoundary_strictTransformIndex] at hmem
        have hone : orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 :=
          hGeom.orderAt_boundary_eq_one (blowupTriple T π q I') hT'.valid _ hstrictmem _ hmem
        rw [hone]
        simp [hi]
      · have hnot : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∉
            (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
              (T.boundary.get i)).support := by
          intro hc
          refine hi ((hmemiff
            (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i)).1 ?_)
          rw [get_transformedBoundary_strictTransformIndex]
          exact hc
        rw [(orderAt_eq_zero_iff_not_mem_support _ _).2 hnot]
        simp [hi]
    have hεval : ε = (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) := by
      by_cases hi : i ∈ lexMaxIndices T.ideal T.mult T.boundary
      · rw [if_pos hi]
        exact hεiff.2 ⟨⊤, trivial, fun y hy => hmaxIdx i hi hy.1⟩
      · rw [if_neg hi]
        rcases hε01 with h0 | h1
        · exact h0
        · exfalso
          obtain ⟨V, hVmem, hVsub⟩ := hεiff.1 h1
          exact hi (hkeyc i V hVmem hVsub)
    rw [hfact, hstrict, hEord, mul_one, hεval, Nat.cast_add]
  have hA : ∑ i : Fin T.boundary.length,
      a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
        then 1 else 0 : ℕ))
      = ∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i := by
    simp [preimageStrictTransformIndex, mul_ite, mul_one, mul_zero, Finset.sum_filter]
  have hB : ∑ i : Fin T.boundary.length,
      a i * ((if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0 : ℕ))
      = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem]
  have hnat : ∑ i : Fin T.boundary.length,
      a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
          then 1 else 0)
        + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
      = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
        + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    calc ∑ i : Fin T.boundary.length,
        a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
            then 1 else 0)
          + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
        = ∑ i : Fin T.boundary.length,
            (a i * (if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
              + a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) :=
          Finset.sum_congr rfl fun i _ => mul_add _ _ _
      _ = (∑ i : Fin T.boundary.length,
            a i * (if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0))
          + ∑ i : Fin T.boundary.length,
            a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) :=
          Finset.sum_add_distrib
      _ = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
          + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by rw [hA, hB]
  have hgoal1 : orderAlong T.ideal C₀
      = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC₀) hmem₀ U hU a hmon
  have ekey : ∑ i : Fin T.boundary.length, (a i : ℕ∞) *
        orderAt ((T.boundary.get i).comap π)
          (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ((∑ i : Fin T.boundary.length,
          a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hoi i, Nat.cast_mul]
  have key : (T.mult : ℕ∞) + orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i : ℕ) : ℕ∞)
        + ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) := by
    rw [← h3, h1, ekey, hnat, Nat.cast_add]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', hgoal1,
    add_comm (orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint) ((T.mult : ℕ∞))]
  exact key

private theorem exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (hr : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary)
    {J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length)}
    {C' : Set ↥X'}
    (hcand : IsCandidateComponent I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      (minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) J' C')
    (hordmax : orderAlong I' C'
      = maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) :
    exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∉ J' := by
  classical
  intro hnew
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth q := hT'.valid.smooth
  have hC'comp : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) J' := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    tauto
  have hC'' : C' ∈ intersectionComponents (blowupTriple T π q I').boundary J' := hC'comp
  have hmemiff : ∀ i : Fin (transformedBoundary π
      (monomialCenter T.ideal T.mult T.boundary) T.boundary).length,
      ((isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
        ((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC'' i
  have hEmem : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support := by
    have hx := (hmemiff (exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).2 hnew
    rwa [get_transformedBoundary_exceptionalIndex] at hx
  have hZmem : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    rw [← Blowup.exceptionalIdeal_eq_comap]
    exact hEmem
  have hπZ : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (monomialCenter T.ideal T.mult T.boundary).support :=
    (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp hZmem
  have hπZset : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := hπZ
  have hcos : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      orderAtLeastLocus T.ideal T.mult := support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hπZset
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ hcos
  have hπcenter : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h]
    exact hπZset
  rw [monomialCenterSet_eq_sUnion_centerComponents] at hπcenter
  obtain ⟨C₀, hC₀, hmem₀⟩ := Set.mem_sUnion.1 hπcenter
  have hformula := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT'
    hnew hC'comp U hU a hmon hC₀ hmem₀
  have hv0 : orderAlong T.ideal C₀ = maxCandidateOrder T.ideal T.mult T.boundary :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C₀).1 hC₀).2
  have hvU : orderAlong I' C' = maxCandidateOrder T.ideal T.mult T.boundary := by rw [hordmax, hv]
  rw [hvU, hv0] at hformula
  have hvlt : maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := (maxCandidateOrder_spec hGeom hT h).2.2.2
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt hvlt)
  rw [← hN] at hformula
  have hnateq : N + T.mult
      = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i) + N := by
    exact_mod_cast hformula
  have hsumeq : (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
      = T.mult := by omega
  have hmpos : 1 ≤ T.mult := hT.valid.one_le_mult
  have hcardpos :
      1 ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card := by
    rcases Finset.eq_empty_or_nonempty
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') with he | hne
    · exfalso
      rw [he, Finset.sum_empty] at hsumeq
      omega
    · exact Finset.card_pos.2 hne
  have hdiv : ∀ j ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
      π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈ (T.boundary.get j).support := by
    intro j hj
    have hj' : strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary j ∈ J' :=
      (mem_preimageStrictTransformIndex_iff π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' j).1 hj
    have hmem := (hmemiff
      (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary j)).2 hj'
    rw [get_transformedBoundary_strictTransformIndex] at hmem
    obtain ⟨ε, hε01, hεiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional hGeom hT h π q hT'.valid.smooth hπ j
        (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint
    have h1 : (1 : ℕ∞) ≤ orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get j)) (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint :=
      (one_le_orderAt_iff_mem_support _ _).2 hmem
    have h2 : (1 : ℕ∞) ≤ orderAt ((T.boundary.get j).comap π)
        (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint := by
      rw [hfact]
      exact le_trans h1 le_self_add
    have h3 : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
        ((T.boundary.get j).comap π).support :=
      (one_le_orderAt_iff_mem_support _ _).1 h2
    exact (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp h3
  have hsupp : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (intersectionIdeal T.boundary
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).support :=
    mem_support_intersectionIdeal T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') _ hdiv
  obtain ⟨C₁, hxC₁, hcomp₁⟩ := exists_isIrreducibleComponentOf_mem
    (↑(intersectionIdeal T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).support :
        Set ↥T.scheme) _ hsupp
  have hC₁ : C₁ ∈ intersectionComponents T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') :=
    (mem_intersectionComponents_iff _ _ _).2 hcomp₁
  have hord₁ : orderAlong T.ideal C₁
      = ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
          a i : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC₁ hxC₁ U hU a hmon
  have hcand₁ : IsCandidateComponent T.ideal T.mult T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') C₁ := by
    unfold IsCandidateComponent
    refine ⟨rfl, hC₁, ?_⟩
    rw [hord₁, hsumeq]
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨_, hcardpos, _, _, hcand₁⟩
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary hex).2.2 _ hcardpos _ _ hcand₁
  have hcardJ' : J'.card = minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    exact hc.1
  have hcard2 : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1
      = J'.card :=
    card_preimageStrictTransformIndex_add_one_of_mem π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' hnew
  rw [hr] at hcardJ'
  omega

theorem maxOrderCandidatePairs_ncard_lt_of_blowup (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (_h' : minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0)
    (hr : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary) :
    (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).ncard
      < (maxOrderCandidatePairs T.ideal T.mult T.boundary).ncard := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth q := hT'.valid.smooth
  have hfinD : (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite :=
    finite_maxOrderCandidatePairs hGeom hT
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C₀, hcand₀, hord₀⟩ := hbest
  have hC₀opt : C₀ ∈ centerComponents T.ideal T.mult T.boundary :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C₀).2 ⟨hcand₀, hord₀⟩
  have hp₀ : (lexMaxIndices T.ideal T.mult T.boundary, C₀)
      ∈ maxOrderCandidatePairs T.ideal T.mult T.boundary :=
    (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨hcand₀, hord₀⟩
  have hπ' : Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)) := by
    rw [← monomialCenter_eq_componentUnionIdeal hGeom hT h]
    exact hπ
  have htc := hGeom.transformed_components T hT.valid
    (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary)
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
    (isOpen_preimage_sUnion_centerComponents hGeom hT) X' π hπ'
  rw [← monomialCenter_eq_componentUnionIdeal hGeom hT h] at htc
  have hkey : ∀ p ∈ maxOrderCandidatePairs I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary),
      ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2)) ∈ maxOrderCandidatePairs T.ideal T.mult T.boundary) ∧
        closure (⇑π '' p.2) ∉ centerComponents T.ideal T.mult T.boundary ∧
        exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∉ p.1 ∧
        p.2 = closure ((⇑π ⁻¹' closure (⇑π '' p.2)) \
          (↑(Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support :
            Set ↥X')) := by
    intro p hp
    obtain ⟨hcand, hordmax⟩ := (mem_maxOrderCandidatePairs_iff I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) p).1 hp
    have hnew := exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder hGeom hT h π q hπ I' hI' hT' hr hv
      hcand hordmax
    have hC'comp : p.2 ∈ intersectionComponents
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) p.1 := by
      have hc := hcand
      unfold IsCandidateComponent at hc
      tauto
    have hC'img : p.2 ∈ intersectionComponents
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1).image
          (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
      rw [image_strictTransformIndex_preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
        hnew]
      exact hC'comp
    have hgen : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC'img).genericPoint p.2 :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC'img
    obtain ⟨hoff, C, hC, hCnot, hC'eq, hlast⟩ :=
      htc (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1) p.2 hC'img _ hgen
    have hCirr : IsIrreducible C := isIrreducible_of_mem_intersectionComponents hC
    have hCcl : IsClosed C := isClosed_intersectionComponents_of_mem hC
    have hgpC : IsGenericPoint hCirr.genericPoint C :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC
    have hπgp : π (isIrreducible_of_mem_intersectionComponents hC'img).genericPoint = hCirr.genericPoint :=
      hlast _ hgpC
    have hclim : closure (⇑π '' p.2) = C := by
      rw [closure_image_genericPoint (f := ⇑π) π.continuous hgen, hπgp, hgpC]
    have hSirr : IsIrreducible (⇑π '' p.2) :=
      (isIrreducible_of_mem_intersectionComponents hC'img).image _ π.continuous.continuousOn
    have hcl2 : closure (⇑π '' p.2) = closure C := by
      rw [hclim, hCcl.closure_eq]
    have hordeq : orderAlong I' p.2 = orderAlong T.ideal C := by
      have h1 := orderAlong_transform_eq_of_genericPoint_not_mem_exceptional hGeom hT h π hπ I' hI' hC'img hoff
      rw [h1]
      exact orderAlong_eq_of_closure_eq T.ideal hSirr hCirr hcl2
    have hordC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordeq, hordmax, hv]
    refine ⟨?_, ?_, hnew, ?_⟩
    · refine (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨?_, ?_⟩
      · unfold IsCandidateComponent
        refine ⟨?_, ?_, ?_⟩
        · rw [card_preimageStrictTransformIndex_of_not_mem π (monomialCenter T.ideal T.mult T.boundary)
            T.boundary p.1 hnew]
          have hc := hcand
          unfold IsCandidateComponent at hc
          rw [hc.1]
          exact hr
        · rw [hclim]
          exact hC
        · rw [hclim, hordC]
          exact (maxCandidateOrder_spec hGeom hT h).2.2.1
      · rw [hclim, hordC]
    · rw [hclim]
      exact hCnot
    · rw [hclim]
      exact hC'eq
  have hinj : Set.InjOn
      (fun p : Finset (Fin (transformedBoundary π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2)))
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
    intro p hp p' hp' heq
    obtain ⟨-, -, hnew1, hrep1⟩ := hkey p hp
    obtain ⟨-, -, hnew2, hrep2⟩ := hkey p' hp'
    have hJ : preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
        = preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p'.1 :=
      congrArg Prod.fst heq
    have hC : closure (⇑π '' p.2) = closure (⇑π '' p'.2) := congrArg Prod.snd heq
    have hfst : p.1 = p'.1 := by
      rw [← image_strictTransformIndex_preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
          hnew1,
        ← image_strictTransformIndex_preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p'.1
          hnew2,
        hJ]
    have hsnd : p.2 = p'.2 := by
      rw [hrep1, hC]
      exact hrep2.symm
    exact Prod.ext hfst hsnd
  have himg : (fun p : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
        closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
      ⊆ maxOrderCandidatePairs T.ideal T.mult T.boundary := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hkey p hp).1
  have hnotin : (lexMaxIndices T.ideal T.mult T.boundary, C₀) ∉
      (fun p : Finset (Fin (transformedBoundary π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
    rintro ⟨p, hp, heq⟩
    have hsnd : closure (⇑π '' p.2) = C₀ := congrArg Prod.snd heq
    refine (hkey p hp).2.1 ?_
    rw [hsnd]
    exact hC₀opt
  have hss : (fun p : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
        closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
      ⊂ maxOrderCandidatePairs T.ideal T.mult T.boundary := by
    refine Set.ssubset_iff_subset_ne.2 ⟨himg, ?_⟩
    intro hEq
    apply hnotin
    rw [hEq]
    exact hp₀
  have hlt := Set.ncard_lt_ncard hss hfinD
  rwa [Set.InjOn.ncard_image hinj] at hlt

end FunctorialResolution.EmbeddedResolution

end
