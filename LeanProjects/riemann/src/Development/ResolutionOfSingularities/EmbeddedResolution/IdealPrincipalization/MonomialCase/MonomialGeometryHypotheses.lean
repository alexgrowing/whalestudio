import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

def pullbackOverField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) : MarkedIdealWithBoundary.{u} where
  base := k'
  instField := inferInstance
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := T.mult
  boundary := T.boundary.map fun D => D.comap h

theorem pullbackOverField_baseField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).base = k' := rfl

@[simp] theorem pullbackOverField_scheme (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).scheme = Y := rfl

theorem pullbackOverField_structureMorphism (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).structMap = q := rfl

@[simp] theorem pullbackOverField_ideal (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).ideal = T.ideal.comap h := rfl

@[simp] theorem pullbackOverField_mult (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).mult = T.mult := rfl

@[simp] theorem pullbackOverField_boundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).boundary = T.boundary.map fun D => D.comap h := rfl

theorem pullbackOverField_eq_pullbackAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    T.pullbackOverField Y T.base q h = T.pullbackAlong Y q h :=
  rfl

theorem pullbackOverField_boundary_length (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).boundary.length = T.boundary.length :=
  List.length_map _

theorem pullbackAlong_boundary_length (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    (T.pullbackAlong Y q h).boundary.length = T.boundary.length :=
  (congrArg List.length (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h)).trans (List.length_map _)

end MarkedIdealWithBoundary

def pullbackOverFieldIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q h).boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q h).symm

theorem pullbackOverFieldIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackOverFieldIndex T Y k' q h j : Fin (T.pullbackOverField Y k' q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl

def pullbackAlongIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackAlong Y q h).boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackAlong_boundary_length T Y q h).symm

theorem pullbackAlongIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q h j : Fin (T.pullbackAlong Y q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl

def IsIrreducibleComponentOf {Y : Scheme.{u}} (C S : Set ↥Y) : Prop :=
  IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C

theorem mem_intersectionComponents_iff {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔ IsIrreducibleComponentOf C ↑(intersectionIdeal L J).support :=
  Iff.rfl

abbrev transformedBoundary {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : List X'.IdealSheafData :=
  L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]

theorem transformedBoundary_length {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) :
    (transformedBoundary π Z L).length = L.length + 1 := by
  simp [transformedBoundary]

def strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (j : Fin L.length) :
    Fin (transformedBoundary π Z L).length :=
  Fin.cast (transformedBoundary_length π Z L).symm j.castSucc

theorem strictTransformIndex_val {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (j : Fin L.length) :
    ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) = (j : ℕ) := rfl

def exceptionalIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : Fin (transformedBoundary π Z L).length :=
  Fin.cast (transformedBoundary_length π Z L).symm (Fin.last L.length)

theorem exceptionalIndex_val {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) :
    ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) = L.length := rfl

def preimageStrictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) : Finset (Fin L.length) :=
  Finset.univ.filter fun j => strictTransformIndex π Z L j ∈ J'

theorem mem_preimageStrictTransformIndex_iff {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) (j : Fin L.length) :
    j ∈ preimageStrictTransformIndex π Z L J' ↔ strictTransformIndex π Z L j ∈ J' := by
  simp [preimageStrictTransformIndex]

def componentUnionOpens {Y : Scheme.{u}} (L : List Y.IdealSheafData) (J : Finset (Fin L.length))
    (𝒞 : Set (Set ↥Y)) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (intersectionIdeal L J).subscheme.Opens :=
  ⟨⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞, hop⟩

def componentUnionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData) (J : Finset (Fin L.length))
    (𝒞 : Set (Set ↥Y)) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    Y.IdealSheafData :=
  Scheme.Hom.ker ((componentUnionOpens L J 𝒞 hop).ι ≫ (intersectionIdeal L J).subschemeι)

theorem componentUnionIdeal_eq_ker {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (𝒞 : Set (Set ↥Y))
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    componentUnionIdeal L J 𝒞 hop =
      Scheme.Hom.ker ((componentUnionOpens L J 𝒞 hop).ι ≫ (intersectionIdeal L J).subschemeι) := rfl

structure MonomialGeometryHypotheses : Prop where
  card_lt_dim : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  flat_comap_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
        𝒞 ⊆ intersectionComponents T.boundary J →
        ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
          ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
                  (J.image (pullbackOverFieldIndex T Y k' q g))).subschemeι ⁻¹'
                ⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
                    (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
                  ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
            (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
              componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
                (J.image (pullbackOverFieldIndex T Y k' q g))
                {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
                    (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
                  ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  center_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        AlgebraicGeometry.Smooth ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  center_support : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞
  blowup_total_transform : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ D ∈ T.boundary, ∀ x' : ↥X',
        ∃ (U' : X'.Opens) (ε : ℕ), x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
          (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆ (↑D.support : Set ↥T.scheme)) ∧
          (D.comap π).comap U'.ι =
            (Blowup.strictTransform π Z D).comap U'.ι * ((Blowup.exceptionalIdeal π Z).comap U'.ι) ^ ε
  flat_components_down : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y),
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (J.image (pullbackOverFieldIndex T Y k' q g)) →
        ∃ C ∈ intersectionComponents T.boundary J,
          Set.MapsTo (⇑g) C' C ∧
            ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  flat_components_up : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        C ∈ intersectionComponents T.boundary J →
        ∀ y : ↥Y, g y ∈ C →
          ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)),
            y ∈ C' ∧
              ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  smooth_components_down : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h],
      h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y),
        C' ∈ intersectionComponents (T.pullbackAlong Y q h).boundary
            (J.image (pullbackAlongIndex T Y q h)) →
        ∃ C ∈ intersectionComponents T.boundary J,
          Set.MapsTo (⇑h) C' C ∧
            ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → h ξ' = ξ
  smooth_components_up : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h],
      h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        C ∈ intersectionComponents T.boundary J →
        ∀ y : ↥Y, h y ∈ C →
          ∃ C' ∈ intersectionComponents (T.pullbackAlong Y q h).boundary
              (J.image (pullbackAlongIndex T Y q h)),
            y ∈ C' ∧
              ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → h ξ' = ξ
  components_disjoint : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      ∀ C ∈ intersectionComponents T.boundary J, ∀ C' ∈ intersectionComponents T.boundary J, C ≠ C' → Disjoint C C'
  components_finite : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length), (intersectionComponents T.boundary J).Finite
  components_subset_divisor_iff : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J →
      ∀ i : Fin T.boundary.length,
        (C ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J)
  transformed_components : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J₀ : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J₀ →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
        Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
        ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥X'),
          C' ∈ intersectionComponents
              (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
              (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)) →
          ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
            ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
              ∃ C ∈ intersectionComponents T.boundary J, C ∉ 𝒞 ∧
                C' = closure ((⇑π ⁻¹' C) \
                    (↑(Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                      Set ↥X')) ∧
                  ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ
  level_schemeDim_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  stratum_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)
  level_valid : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length → (T.transformAt s i).IsAdmissible
  orderAt_bounded : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ I : T.scheme.IdealSheafData, NonzeroOnComponents I →
      ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt I x ≤ (B : ℕ∞)
  orderAt_comap_off_exceptional : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ x' : ↥X', x' ∉ (Blowup.exceptionalIdeal π Z).support →
        ∀ A : T.scheme.IdealSheafData, orderAt (A.comap π) x' = orderAt A (π x')
  orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1
  sUnion_isOpen : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)
  withBoundary_valid : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ E' : List T.scheme.IdealSheafData, MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E' →
      (T.withBoundary E').IsAdmissible

end FunctorialResolution.EmbeddedResolution

end
