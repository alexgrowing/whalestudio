import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

open scoped Classical

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

noncomputable def balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : T.scheme.IdealSheafData :=
  @balancedTunedSheaf T.base _ _ T.scheme T.structMap hv.locallyOfFiniteType T.ideal T.mult

abbrev tunedMult (T : MarkedIdealWithBoundary.{u}) : ℕ := tuningExponent T.mult

noncomputable def chosenCoverData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactReduction.FiniteOpenCoverWithIdeals T :=
  MaxContactReduction.maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)

theorem isMaxContactCover_maxContactCover (T : MarkedIdealWithBoundary.{u})
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T, MaxContactReduction.IsMaxContactCover T D hft W μ) :
    MaxContactReduction.IsMaxContactCover T (MaxContactReduction.maxContactCover T hft W μ) hft W μ := by
  have he : MaxContactReduction.maxContactCover T hft W μ = h.choose := dif_pos h
  rw [he]
  exact h.choose_spec

theorem isMaxContactCover_chosenCoverData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T) :=
  isMaxContactCover_maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T) h

@[reducible] noncomputable def coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion ⟶ T.scheme :=
  (chosenCoverData T hv).disjointUnionMap

theorem coverMap_eq_sigmaOpensDesc (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    coverMap T hv = sigmaOpensDesc T.scheme (chosenCoverData T hv).opens := rfl

theorem etale_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact etale_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instEtaleCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) :=
  etale_coverMap_of_isAdmissible T hv

theorem smooth_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Smooth (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instSmoothCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Smooth (coverMap T hv) :=
  smooth_coverMap_of_isAdmissible T hv

theorem flat_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Flat (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instFlatCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Flat (coverMap T hv) :=
  flat_coverMap_of_isAdmissible T hv

theorem locallyOfFiniteType_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact locallyOfFiniteType_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instLocallyOfFiniteTypeCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) :=
  locallyOfFiniteType_coverMap T hv

@[reducible] noncomputable def coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion.IdealSheafData :=
  (chosenCoverData T hv).iInfImageIdeal

noncomputable def coverTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} :=
  (chosenCoverData T hv).markedTriple (balancedTunedIdeal T hv) (tunedMult T)

@[simp] theorem coverTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).scheme = (chosenCoverData T hv).disjointUnion := rfl

@[simp] theorem coverTriple_baseField (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).base = T.base := rfl

@[simp] theorem coverTriple_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).structMap = coverMap T hv ≫ T.structMap := rfl

@[simp] theorem coverTriple_ideal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).ideal = (balancedTunedIdeal T hv).comap (coverMap T hv) := rfl

@[simp] theorem coverTriple_mult (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).mult = tunedMult T := rfl

@[simp] theorem coverTriple_boundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).boundary = T.boundary.map (fun D => D.comap (coverMap T hv)) := rfl

@[simp] theorem coverTriple_dim (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).krullDimSucc = krullDimSucc (chosenCoverData T hv).disjointUnion := rfl

noncomputable def coverMarkedBlowupData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData (coverTriple T hv).structMap (coverTriple T hv).ideal
      (coverTriple T hv).mult (coverTriple T hv).boundary :=
  MaxContactReduction.reduceAlongHypersurface hinv T rc (coverTriple T hv) (coverMaxContactIdeal T hv)

theorem cover_eq_reduceAlongHypersurface (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    coverMarkedBlowupData T hv hinv rc =
      MaxContactReduction.reduceAlongHypersurface hinv T rc (coverTriple T hv) (coverMaxContactIdeal T hv) := rfl

theorem isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some {T S : MarkedIdealWithBoundary.{u}} (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) {d : BlowupSequenceData T.scheme}
    (hd : MaxContactReduction.descendStrictPullback T S φ s = some d) :
    IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups := by
  by_cases hex : ∃ e : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups e.toSequenceOfBlowups
  · have he : MaxContactReduction.descendStrictPullback T S φ s = some hex.choose := dif_pos hex
    rw [he] at hd
    have h2 : hex.choose = d := Option.some.inj hd
    exact h2 ▸ hex.choose_spec
  · have he : MaxContactReduction.descendStrictPullback T S φ s = none := dif_neg hex
    rw [he] at hd
    simp at hd

theorem exists_descendStrictPullback_eq_some {T S : MarkedIdealWithBoundary.{u}} (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (h : ∃ d : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∃ d : BlowupSequenceData T.scheme, MaxContactReduction.descendStrictPullback T S φ s = some d :=
  ⟨h.choose, dif_pos h⟩

theorem asMarkedSeq_eq_toMarkedSequence_of_isMarked (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme)
    (h : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.asMarkedSeq T d =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups :=
  dif_pos h

theorem asMarkedSeq_toSequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme)
    (h : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    (MaxContactReduction.asMarkedSeq T d).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  rw [asMarkedSeq_eq_toMarkedSequence_of_isMarked T d h,
    BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]

theorem reduceOrder_eq_asMarkedSeq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅)
    (htrim : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible) (d : BlowupSequenceData T.scheme)
    (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
        (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d) :
    MaxContactReduction.reduceOrder hinv T rc = MaxContactReduction.asMarkedSeq T d := by
  have key : MaxContactReduction.reduceOrderOfValid hinv T rc hv = MaxContactReduction.asMarkedSeq T d := by
    show (match MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) with
          | some e => MaxContactReduction.asMarkedSeq T e
          | none => MaxContactReduction.emptyMarkedSeq T) = MaxContactReduction.asMarkedSeq T d
    rw [hd]
  unfold MaxContactReduction.reduceOrder
  rw [dif_pos hv, if_neg hne, key]

theorem reduceOrder_eq_toMarkedSequence (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅)
    (htrim : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible) (d : BlowupSequenceData T.scheme)
    (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
        (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d)
    (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.reduceOrder hinv T rc =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  rw [reduceOrder_eq_asMarkedSeq hinv T rc hv hne htrim d hd, asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]

@[simp] theorem emptyMarkedSeq_length (T : MarkedIdealWithBoundary.{u}) :
    (MaxContactReduction.emptyMarkedSeq T).length = 0 :=
  emptyMarkedBlowupSequenceData_toMarkedSequence_length T.structMap T.ideal T.mult T.boundary

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem asMarkedData_eq_some_of_isMarked (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.asMarkedData s d =
      some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h) :=
  dif_pos h

theorem concatOfIsMarked_eq_append_of_isMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.concatOfIsMarked hinv s d =
      s.append (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
        (s.boundary s.length) h) hinv := by
  have hr := asMarkedData_eq_some_of_isMarked s d h
  show (match MaxContactReduction.asMarkedData s d with
        | some t => s.append t hinv
        | none => s) = _
  rw [hr]

end

noncomputable def derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} :=
  MaxContactReduction.tunedTriple S s hft extra keep

@[simp] theorem derivedTriple_scheme (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).scheme = s.obj s.length := rfl

@[simp] theorem derivedTriple_mult (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).mult = tuningExponent S.mult := rfl

@[simp] theorem derivedTriple_boundary (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).boundary = extra ++ (s.boundary s.length).drop keep := rfl

theorem derivedTriple_structureMorphism (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).structMap = s.proj s.length ≫ S.structMap := rfl

theorem appendLowerDimReduction_eq_concatOfIsMarked (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n =
      MaxContactReduction.concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (rc (derivedTriple S s hft extra keep) hdim n).toSequenceOfBlowups) := by
  unfold MaxContactReduction.appendLowerDimReduction
  rw [dif_pos hft]
  exact dif_pos hdim

theorem appendLowerDimReduction_of_not_locallyOfFiniteType (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : ¬ LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n = s := by
  unfold MaxContactReduction.appendLowerDimReduction
  exact dif_neg hft

@[simp] theorem separateBoundary_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) :
    MaxContactReduction.separateBoundary hinv T rc S 0 =
      emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary := rfl

theorem separateBoundary_succ (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T rc S (j + 1) =
      MaxContactReduction.appendLowerDimReduction hinv T rc S (MaxContactReduction.separateBoundary hinv T rc S j) [] 0 j := rfl

theorem reduceAlongHypersurface_eq_appendLowerDimReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (H : S.scheme.IdealSheafData) :
    MaxContactReduction.reduceAlongHypersurface hinv T rc S H =
      MaxContactReduction.appendLowerDimReduction hinv T rc S
        (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length)
        [MaxContactReduction.strictTransformAtLength (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length) H]
        S.boundary.length 0 := rfl

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
