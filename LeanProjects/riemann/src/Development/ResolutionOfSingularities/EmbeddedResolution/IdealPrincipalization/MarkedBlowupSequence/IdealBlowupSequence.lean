import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure SmoothCenterBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : Type (u + 1) where
  center : X.IdealSheafData
  center_smooth : AlgebraicGeometry.Smooth (center.subschemeι ≫ p)
  center_snc : HasStrictNormalCrossingsWith p center E
  ideal_vanishes : VanishesAlong I center
  obj : Scheme.{u}
  map : obj ⟶ X
  isBlowup : Blowup.IsBlowupAlongIdealSheaf map center
  idealUp : obj.IdealSheafData
  transform_rule : Blowup.exceptionalIdeal map center * idealUp = I.comap map

namespace SmoothCenterBlowup

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : SmoothCenterBlowup p I E) : s.obj ⟶ Spec (CommRingCat.of k) := s.map ≫ p

theorem structureMorphism_eq (s : SmoothCenterBlowup p I E) : s.structureMorphism = s.map ≫ p := rfl

def exceptionalIdeal (s : SmoothCenterBlowup p I E) : s.obj.IdealSheafData :=
  Blowup.exceptionalIdeal s.map s.center

theorem exceptionalIdeal_eq (s : SmoothCenterBlowup p I E) : s.exceptionalIdeal = s.center.comap s.map := rfl

def boundary (s : SmoothCenterBlowup p I E) : List s.obj.IdealSheafData :=
  E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal]

theorem boundary_eq (s : SmoothCenterBlowup p I E) :
    s.boundary = E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal] := rfl

end SmoothCenterBlowup

structure IdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap (toSequenceOfBlowups.projectionToBase 0)
  boundary_zero : boundary 0 = E.map (fun D => D.comap (toSequenceOfBlowups.projectionToBase 0))
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  ideal_vanishes : ∀ i, i < toSequenceOfBlowups.length →
    VanishesAlong (ideal i) (toSequenceOfBlowups.center i)
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

theorem structureMorphism_def (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.structureMorphism i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

theorem smooth_center_subschemeι (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.structureMorphism i) :=
  s.center_smooth i h

theorem hasStrictNormalCrossingsWith_center (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) (s.boundary i) :=
  s.center_snc i h

def exceptionalIdeal (s : IdealBlowupSequence p I E) (i : ℕ) : (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

theorem exceptionalIdeal_eq (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

theorem boundary_succ_eq_map_strictTransform_append (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    s.boundary (i + 1) =
      (s.boundary i).map
          (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)) ++
        [s.exceptionalIdeal i] :=
  s.boundary_succ i h

def lastIdeal (s : IdealBlowupSequence p I E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq (s : IdealBlowupSequence p I E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

def lastBoundary (s : IdealBlowupSequence p I E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length

theorem lastBoundary_eq (s : IdealBlowupSequence p I E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := rfl

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution
