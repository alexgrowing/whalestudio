import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory

namespace GlobalTheory

section Morphisms

variable {X Y S : Scheme.{u}}

theorem isNormalScheme_of_smooth (f : X ⟶ S) [Smooth f] [IsNormalScheme S] : IsNormalScheme X :=
  (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff S).mp ‹_›))

theorem isIntegral_of_smooth_of_connectedSpace (f : X ⟶ S) [Smooth f] [IsNormalScheme S]
    [IsLocallyNoetherian S] [ConnectedSpace X] : IsIntegral X :=
  have := isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  IsNormalScheme.isIntegral_of_connectedSpace X

theorem isIntegral_of_smooth_field {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) [Smooth f]
    [ConnectedSpace X] : IsIntegral X :=
  isIntegral_of_smooth_of_connectedSpace f

theorem geometricallyReduced_of_smooth (f : X ⟶ S) [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback h ‹_›
  have := isNormalScheme_of_smooth snd
  exact IsNormalScheme.isReduced

theorem geometricallyIntegral_of_smooth (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback h ‹_›
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field snd

theorem geometricallyConnected_of_geometricallyIntegral (f : X ⟶ S) [GeometricallyIntegral f] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  exact inferInstanceAs (ConnectedSpace Z)

theorem isIntegral_of_geometricallyIntegral (f : X ⟶ S) [GeometricallyIntegral f] [Flat f]
    [UniversallyOpen f] [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩

theorem isIntegral_of_smooth_of_geometricallyConnected (f : X ⟶ S) [Smooth f]
    [GeometricallyConnected f] [IsIntegral S] : IsIntegral X :=
  have := geometricallyIntegral_of_smooth f
  isIntegral_of_geometricallyIntegral f

theorem isIntegral_of_isPullback_of_smooth {Z : Scheme.{u}} {fst : Z ⟶ X} {snd : Z ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) [Smooth f] [GeometricallyConnected f]
    [IsIntegral Y] : IsIntegral Z :=
  have : Smooth snd := MorphismProperty.of_isPullback h ‹_›
  have : GeometricallyConnected snd := MorphismProperty.of_isPullback h ‹_›
  isIntegral_of_smooth_of_geometricallyConnected snd

theorem isIntegral_pullback_of_smooth (f : X ⟶ S) (g : Y ⟶ S) [Smooth f]
    [GeometricallyConnected f] [IsIntegral Y] : IsIntegral (pullback f g) :=
  isIntegral_of_isPullback_of_smooth (.of_hasPullback f g)

theorem isIntegral_fiber_of_smooth (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] (s : S) :
    IsIntegral (f.fiber s) :=
  have := geometricallyIntegral_of_smooth f
  inferInstance

theorem geometricallyConnected_of_isIso (f : X ⟶ S) [IsIso f] : GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : IsIso snd := h.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous

end Morphisms

section Products

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}}

theorem smooth_tensorObj_hom (G H : Over S) [Smooth G.hom] [Smooth H.hom] :
    Smooth (G ⊗ H).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

theorem geometricallyConnected_tensorObj_hom (G H : Over S) [Smooth G.hom] [Smooth H.hom]
    [GeometricallyConnected G.hom] [GeometricallyConnected H.hom] :
    GeometricallyConnected (G ⊗ H).hom := by
  rw [Over.tensorObj_hom]
  exact GeometricallyConnected.comp _ _

theorem geometricallyIntegral_tensorObj_hom (G H : Over S) [Smooth G.hom] [Smooth H.hom]
    [GeometricallyConnected G.hom] [GeometricallyConnected H.hom] :
    GeometricallyIntegral (G ⊗ H).hom :=
  have := smooth_tensorObj_hom G H
  have := geometricallyConnected_tensorObj_hom G H
  geometricallyIntegral_of_smooth _

open ReciprocityTheory.ChartRestriction.G.Semi

variable (G : Over S) [Smooth G.hom]

theorem smooth_square_hom : Smooth (G2 G).hom := smooth_tensorObj_hom G G

theorem smooth_cube_hom : Smooth (G3 G).hom :=
  have := smooth_square_hom G
  smooth_tensorObj_hom G (G2 G)

theorem smooth_fourthPower_hom : Smooth (G4 G).hom :=
  have := smooth_cube_hom G
  smooth_tensorObj_hom G (G3 G)

variable [GeometricallyConnected G.hom]

theorem geometricallyConnected_square_hom : GeometricallyConnected (G2 G).hom :=
  geometricallyConnected_tensorObj_hom G G

theorem geometricallyConnected_cube_hom : GeometricallyConnected (G3 G).hom :=
  have := smooth_square_hom G
  have := geometricallyConnected_square_hom G
  geometricallyConnected_tensorObj_hom G (G2 G)

theorem geometricallyConnected_fourthPower_hom : GeometricallyConnected (G4 G).hom :=
  have := smooth_cube_hom G
  have := geometricallyConnected_cube_hom G
  geometricallyConnected_tensorObj_hom G (G3 G)

theorem geometricallyIntegral_square_hom : GeometricallyIntegral (G2 G).hom :=
  have := smooth_square_hom G
  have := geometricallyConnected_square_hom G
  geometricallyIntegral_of_smooth _

theorem geometricallyIntegral_cube_hom : GeometricallyIntegral (G3 G).hom :=
  have := smooth_cube_hom G
  have := geometricallyConnected_cube_hom G
  geometricallyIntegral_of_smooth _

theorem geometricallyIntegral_fourthPower_hom : GeometricallyIntegral (G4 G).hom :=
  have := smooth_fourthPower_hom G
  have := geometricallyConnected_fourthPower_hom G
  geometricallyIntegral_of_smooth _

theorem isIntegral_square_left [IsIntegral S] : IsIntegral (G2 G).left :=
  have := smooth_square_hom G
  have := geometricallyConnected_square_hom G
  isIntegral_of_smooth_of_geometricallyConnected (G2 G).hom

theorem isIntegral_cube_left [IsIntegral S] : IsIntegral (G3 G).left :=
  have := smooth_cube_hom G
  have := geometricallyConnected_cube_hom G
  isIntegral_of_smooth_of_geometricallyConnected (G3 G).hom

theorem isIntegral_fourthPower_left [IsIntegral S] : IsIntegral (G4 G).left :=
  have := smooth_fourthPower_hom G
  have := geometricallyConnected_fourthPower_hom G
  isIntegral_of_smooth_of_geometricallyConnected (G4 G).hom

end Products

section Powers

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}} (G : Over S) [Smooth G.hom]

theorem smooth_powObj_hom : ∀ n : ℕ, Smooth (powObj G n).hom
  | 0 => inferInstanceAs (Smooth (𝟙 S))
  | n + 1 =>
    have := smooth_powObj_hom n
    smooth_tensorObj_hom G (powObj G n)

variable [GeometricallyConnected G.hom]

end Powers

section Local

variable {X : Scheme.{u}} {V : Type u} [CommRing V]

theorem isIntegral_specialFibre_of_smooth [IsLocalRing V] (f : X ⟶ Spec (.of V)) [Smooth f]
    [GeometricallyConnected f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) :=
  isIntegral_pullback_of_smooth _ _

theorem isIntegral_genericFibre_of_smooth [IsDomain V] (K : Type u) [Field K] [Algebra V K]
    [IsFractionRing V K] (f : X ⟶ Spec (.of V)) [Smooth f] [GeometricallyConnected f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :=
  isIntegral_pullback_of_smooth _ _

end Local

section Groups

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{u}}

theorem geometricallyIntegral_of_isAbelianScheme (A : Over S) [GrpObj A] [h : IsAbelianScheme A] :
    GeometricallyIntegral A.hom :=
  have := h.smooth
  have := h.geomConnected
  geometricallyIntegral_of_smooth _

theorem geometricallyIntegral_of_isSemiAbelian (G : Over S) [GrpObj G] [h : IsSemiAbelian G] :
    GeometricallyIntegral G.hom :=
  have := h.smooth
  have := h.geomConnected
  geometricallyIntegral_of_smooth _

theorem isIntegral_left_of_isAbelianScheme (A : Over S) [GrpObj A] [h : IsAbelianScheme A]
    [IsIntegral S] : IsIntegral A.left :=
  have := h.smooth
  have := h.geomConnected
  isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem isIntegral_left_of_isSemiAbelian (G : Over S) [GrpObj G] [h : IsSemiAbelian G]
    [IsIntegral S] : IsIntegral G.left :=
  have := h.smooth
  have := h.geomConnected
  isIntegral_of_smooth_of_geometricallyConnected G.hom

end Groups

section Main

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem geometricallyIntegral_of_smooth_of_geometricallyConnected :
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f],
      GeometricallyIntegral f ∧ (IsIntegral S → IsIntegral X)) ∧
    (∀ {S : Scheme.{u}} (A : Over S) [GrpObj A], IsAbelianScheme A ∨ IsSemiAbelian A →
      ∀ T ∈ [A, G2 A, G3 A, G4 A],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ {S : Scheme.{u}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom],
      ∀ T ∈ [G, G2 G, G3 G, G4 G],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
      [Smooth G.hom] [GeometricallyConnected G.hom], ∀ T ∈ [G, G2 G, G3 G, G4 G],
        IsIntegral T.left ∧ IsLocallyNoetherian T.left ∧
        IsIntegral (pullback T.hom (spMap (IsLocalRing.residue V))) ∧
        IsIntegral (pullback T.hom (spMap (algebraMap V (FractionRing V))))) := by
  have key : ∀ {S : Scheme.{u}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom],
      ∀ T ∈ [G, G2 G, G3 G, G4 G],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left) := by
    intro S G _ _ T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact ⟨geometricallyIntegral_of_smooth _,
        fun _ ↦ isIntegral_of_smooth_of_geometricallyConnected T.hom⟩
    · exact ⟨geometricallyIntegral_square_hom G, fun _ ↦ isIntegral_square_left G⟩
    · exact ⟨geometricallyIntegral_cube_hom G, fun _ ↦ isIntegral_cube_left G⟩
    · exact ⟨geometricallyIntegral_fourthPower_hom G, fun _ ↦ isIntegral_fourthPower_left G⟩
  refine ⟨fun f _ _ ↦ ⟨geometricallyIntegral_of_smooth f,
    fun _ ↦ isIntegral_of_smooth_of_geometricallyConnected f⟩, ?_, key, ?_⟩
  · rintro S A _ (h | h)
    all_goals
      have := h.smooth
      have := h.geomConnected
      exact key A
  · intro V _ _ _ G _ _ T hT
    obtain ⟨_, _⟩ : Smooth T.hom ∧ GeometricallyConnected T.hom := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact ⟨‹_›, ‹_›⟩
      · exact ⟨smooth_square_hom G, geometricallyConnected_square_hom G⟩
      · exact ⟨smooth_cube_hom G, geometricallyConnected_cube_hom G⟩
      · exact ⟨smooth_fourthPower_hom G, geometricallyConnected_fourthPower_hom G⟩
    exact ⟨isIntegral_of_smooth_of_geometricallyConnected T.hom,
      LocallyOfFiniteType.isLocallyNoetherian T.hom, isIntegral_specialFibre_of_smooth T.hom,
      isIntegral_genericFibre_of_smooth (FractionRing V) T.hom⟩

end Main

end GlobalTheory
