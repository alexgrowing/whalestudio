import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped Classical

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

def emptyMarkedSeq (T : MarkedIdealWithBoundary.{u}) : T.SequenceOfBlowups :=
  (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups

def IsMaxContactCoord (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

structure FiniteOpenCoverWithIdeals (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) where
  idx : Type u
  finiteIdx : Finite idx
  opens : idx → T.scheme.Opens
  localIdeal : (i : idx) → (opens i).toScheme.IdealSheafData

instance instFiniteCoverIdx {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Finite D.idx :=
  D.finiteIdx

structure IsMaxContactCover (T : MarkedIdealWithBoundary.{u}) (D : FiniteOpenCoverWithIdeals T)
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ) : Prop where
  covers : iSup D.opens = ⊤
  isAffine : ∀ i : D.idx, IsAffineOpen (D.opens i)
  dichotomy : ∀ i : D.idx,
    (Disjoint (orderAtLeastLocus W μ) ((D.opens i : T.scheme.Opens) : Set ↥T.scheme) ∧
      D.localIdeal i = ⊤) ∨
    (∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
      D.localIdeal i = c.coordIdeal {j} ∧
        @IsMaxContactCoord T.base _ T.scheme T.structMap hft W μ (D.opens i) n c j)

def trivialCover (T : MarkedIdealWithBoundary.{u}) : FiniteOpenCoverWithIdeals T where
  idx := PUnit.{u + 1}
  finiteIdx := inferInstance
  opens := fun _ => ⊤
  localIdeal := fun _ => ⊤

def maxContactCover (T : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType T.structMap)
    (W : T.scheme.IdealSheafData) (μ : ℕ) : FiniteOpenCoverWithIdeals T :=
  if h : ∃ D : FiniteOpenCoverWithIdeals T, IsMaxContactCover T D hft W μ then h.choose else trivialCover T

def FiniteOpenCoverWithIdeals.disjointUnion {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Scheme.{u} :=
  sigmaOpens T.scheme D.opens

def FiniteOpenCoverWithIdeals.disjointUnionMap {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion ⟶ T.scheme :=
  sigmaOpensDesc T.scheme D.opens

def FiniteOpenCoverWithIdeals.ι {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.opens i).toScheme ⟶ D.disjointUnion :=
  Sigma.ι (fun i => (D.opens i).toScheme) i

def FiniteOpenCoverWithIdeals.iInfImageIdeal {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion.IdealSheafData :=
  ⨅ i : D.idx, imageIdealSheaf (D.ι i) (D.localIdeal i)

def FiniteOpenCoverWithIdeals.markedTriple {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (W : T.scheme.IdealSheafData)
    (μ : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := D.disjointUnion
  structMap := D.disjointUnionMap ≫ T.structMap
  ideal := W.comap D.disjointUnionMap
  mult := μ
  boundary := T.boundary.map (fun Dv => Dv.comap D.disjointUnionMap)

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def iteratedStrictTransform (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (i : ℕ) → (s.obj i).IdealSheafData
  | 0 => H.comap s.isoZero.hom
  | i + 1 => Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i)

theorem iteratedStrictTransform_zero (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    iteratedStrictTransform s H 0 = H.comap s.isoZero.hom := rfl

theorem iteratedStrictTransform_succ (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ) :
    iteratedStrictTransform s H (i + 1) =
      Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i) := rfl

def strictTransformAtLength (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (s.obj s.length).IdealSheafData :=
  iteratedStrictTransform s H s.length

theorem strictTransformAtLength_eq (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    strictTransformAtLength s H = iteratedStrictTransform s H s.length := rfl

def asMarkedData (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length)) :
    Option (MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :=
  if h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) then
    some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h)
  else
    none

def concatOfIsMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length)) : MarkedBlowupSequenceData p I m E :=
  match asMarkedData s d with
  | some t => s.append t hinv
  | none => s

end

def tunedIdeal (S : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType S.structMap) :
    S.scheme.IdealSheafData :=
  @balancedTunedSheaf S.base _ _ S.scheme S.structMap hft S.ideal S.mult

def tunedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} where
  base := S.base
  instField := S.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ S.structMap
  ideal :=
    @balancedTunedSheaf S.base _ _ (s.obj s.length) (s.proj s.length ≫ S.structMap) hft
      (s.ideal s.length) S.mult
  mult := tuningExponent S.mult
  boundary := extra ++ (s.boundary s.length).drop keep

def appendLowerDimReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ) :
    MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  if hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) then
    if hdim : (tunedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc then
      concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (resolveLower (tunedTriple S s hft extra keep) hdim n).toSequenceOfBlowups)
    else s
  else s

def separateBoundary (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) :
    ℕ → MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | 0 => emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | j + 1 => appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S j) [] 0 j

def reduceAlongHypersurface (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (H : S.scheme.IdealSheafData) : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S S.boundary.length)
    [strictTransformAtLength (separateBoundary hinv T resolveLower S S.boundary.length) H] S.boundary.length 0

def descendStrictPullback (T S : MarkedIdealWithBoundary.{u}) (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    Option (BlowupSequenceData T.scheme) :=
  if h : ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups then
    some h.choose
  else
    none

def asMarkedSeq (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if h : d.IsMarked T.structMap T.ideal T.mult T.boundary then
    (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups
  else
    emptyMarkedSeq T

def dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) : MarkedIdealWithBoundary.{u} :=
  T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤)))

theorem dropTrivialBoundary_def (T : MarkedIdealWithBoundary.{u}) :
    dropTrivialBoundary T = T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤))) := rfl

@[simp] theorem dropTrivialBoundary_baseField (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).base = T.base := rfl

@[simp] theorem dropTrivialBoundary_scheme (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).scheme = T.scheme := rfl

@[simp] theorem dropTrivialBoundary_structureMorphism (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).structMap = T.structMap := rfl

@[simp] theorem dropTrivialBoundary_ideal (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).ideal = T.ideal := rfl

@[simp] theorem dropTrivialBoundary_mult (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).mult = T.mult := rfl

@[simp] theorem dropTrivialBoundary_dim (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).krullDimSucc = T.krullDimSucc := rfl

theorem dropTrivialBoundary_boundary (T : MarkedIdealWithBoundary.{u}) :
    (dropTrivialBoundary T).boundary = T.boundary.filter (fun D => decide (D ≠ ⊤)) := rfl

def reduceOrderOfValid (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible) : T.SequenceOfBlowups :=
  have hft : LocallyOfFiniteType (dropTrivialBoundary T).structMap := hv.locallyOfFiniteType
  let W := tunedIdeal (dropTrivialBoundary T) hft
  let μ := tuningExponent (dropTrivialBoundary T).mult
  let D := maxContactCover (dropTrivialBoundary T) hft W μ
  let S := D.markedTriple W μ
  match descendStrictPullback (dropTrivialBoundary T) S D.disjointUnionMap (reduceAlongHypersurface hinv (dropTrivialBoundary T) resolveLower S D.iInfImageIdeal) with
  | some d => asMarkedSeq T d
  | none => emptyMarkedSeq T

def reduceOrder (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) : T.SequenceOfBlowups :=
  if hv : T.IsAdmissible then
    if orderAtLeastLocus T.ideal T.mult = ∅ then emptyMarkedSeq T else reduceOrderOfValid hinv T resolveLower hv
  else
    emptyMarkedSeq T

theorem reduceOrder_of_orderAtLeastLocus_eq_empty (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = ∅) : reduceOrder hinv T resolveLower = emptyMarkedSeq T := by
  unfold reduceOrder
  rw [dif_pos hv, if_pos h]

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
