import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialInvariantDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BlowupAtMonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def tripleAtLastBlowup (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk T.base T.instField (s.obj s.length)
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)

@[simp]
theorem tripleAtLastBlowup_baseField (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).base = T.base := rfl

@[simp]
theorem tripleAtLastBlowup_scheme (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).scheme = s.obj s.length := rfl

@[simp]
theorem tripleAtLastBlowup_structureMorphism (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).structMap = s.proj s.length ≫ T.structMap := rfl

@[simp]
theorem tripleAtLastBlowup_ideal (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).ideal = s.ideal s.length := rfl

@[simp]
theorem tripleAtLastBlowup_mult (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).mult = T.mult := rfl

@[simp]
theorem tripleAtLastBlowup_boundary (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).boundary = s.boundary s.length := rfl

noncomputable abbrev monomialIterateFromEmpty (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (n : ℕ) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  MarkedBlowupSequenceData.monomialBlowupIterate hinv
    (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n

noncomputable abbrev monomialStallIndexOfTriple (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) : ℕ :=
  monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary

theorem minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0 := by
  intro h0
  exact h.1 (monomialCenter_eq_top_of_minIndexCard_eq_zero (s.ideal s.length) T.mult
    (s.boundary s.length) h0)

theorem isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero (hGeom : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hs : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T s))
    (h : minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0) :
    MarkedBlowupSequenceData.IsAdmissibleCenter s :=
  monomialCenter_spec hGeom hs h

private theorem tripleAtLastBlowup_eq_mk_of_length_eq (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (n : ℕ) (hn : s.length = n) :
    tripleAtLastBlowup T s =
      @MarkedIdealWithBoundary.mk T.base T.instField (s.obj n) (s.proj n ≫ T.structMap) (s.ideal n) T.mult
        (s.boundary n) := by
  subst hn
  rfl

private theorem markedIdealWithBoundary_mk_comap_eqToHom {k : Type u} [instk : Field k] {A B : Scheme.{u}}
    (hAB : A = B) (q : B ⟶ Spec (CommRingCat.of k)) (J : B.IdealSheafData) (m : ℕ)
    (E : List B.IdealSheafData) :
    @MarkedIdealWithBoundary.mk k instk A (eqToHom hAB ≫ q) (J.comap (eqToHom hAB)) m
        (List.map (fun D => D.comap (eqToHom hAB)) E) =
      @MarkedIdealWithBoundary.mk k instk B q J m E := by
  subst hAB
  refine MarkedIdealWithBoundary.mk_eq_mk _ _ ?_ ?_ ?_ <;> simp

private theorem blowupAtCenter_eq_self_of_not_isAdmissibleCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    MarkedBlowupSequenceData.blowupAtCenter hinv s = s := by
  unfold MarkedBlowupSequenceData.blowupAtCenter
  rw [dif_neg h]

private theorem isLocallyMonomialTriple_tripleAtLastBlowup_blowupAtCenter
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hs : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T s)) :
    MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s)) := by
  by_cases hstep : MarkedBlowupSequenceData.IsAdmissibleCenter s
  · have hlen := MarkedBlowupSequenceData.blowupAtCenter_length hinv s hstep
    have hobj := MarkedBlowupSequenceData.blowupAtCenter_schemeAt_succ hinv s hstep
    have hideal := MarkedBlowupSequenceData.blowupAtCenter_ideal_succ hinv s hstep
    have hbdry := MarkedBlowupSequenceData.blowupAtCenter_boundary_succ hinv s hstep
    have hproj := MarkedBlowupSequenceData.blowupAtCenter_projectionToBase_succ hinv s hstep
    have hmin := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T s hstep
    have key : tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s) =
        blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq T (MarkedBlowupSequenceData.blowupAtCenter hinv s) (s.length + 1)
          hlen, hproj, hideal, hbdry]
      simp only [Category.assoc]
      exact markedIdealWithBoundary_mk_comap_eqToHom hobj _ _ _ _
    rw [key]
    exact isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hs hmin
  · rw [blowupAtCenter_eq_self_of_not_isAdmissibleCenter hinv s hstep]
    exact hs

theorem isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (n : ℕ) :
    MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
  induction n with
  | zero =>
    have h0 : monomialIterateFromEmpty hinv T 0 =
        emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
      MarkedBlowupSequenceData.monomialBlowupIterate_zero hinv _
    rw [h0]
    have hT0 : tripleAtLastBlowup T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = T := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) 0
        (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
      exact MarkedIdealWithBoundary.mk_eq_mk T.scheme T.mult (Category.id_comp T.structMap)
        (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
        (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
    rw [hT0]
    exact hT
  | succ n ih =>
    have hstep : monomialIterateFromEmpty hinv T (n + 1) =
        MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T n) :=
      MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv _ n
    rw [hstep]
    exact isLocallyMonomialTriple_tripleAtLastBlowup_blowupAtCenter hGeom hinv T
      (monomialIterateFromEmpty hinv T n) ih

theorem minIndexCard_monomialIterateFromEmpty_ne_zero (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (n : ℕ) (hn : n < monomialStallIndexOfTriple hinv T) :
    minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).boundary ≠ 0 :=
  minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n)
    (isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn)

private theorem tripleAtLastBlowup_blowupAtCenter (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hstep : MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
  have hlen := MarkedBlowupSequenceData.blowupAtCenter_length hinv s hstep
  have hobj := MarkedBlowupSequenceData.blowupAtCenter_schemeAt_succ hinv s hstep
  have hideal := MarkedBlowupSequenceData.blowupAtCenter_ideal_succ hinv s hstep
  have hbdry := MarkedBlowupSequenceData.blowupAtCenter_boundary_succ hinv s hstep
  have hproj := MarkedBlowupSequenceData.blowupAtCenter_projectionToBase_succ hinv s hstep
  simp only [tripleAtLastBlowup]
  rw [hlen, hideal, hbdry, hproj]
  simp only [Category.assoc]
  exact @markedIdealWithBoundary_mk_comap_eqToHom T.base T.instField _ _ hobj _ _ _ _

private theorem exists_isStationaryAt_emptyMarkedBlowupSequenceData (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n := by
  by_contra hcon
  have hstepAll : ∀ n : ℕ, MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) := by
    intro n
    by_contra hn
    exact hcon ⟨n, (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n).mpr hn⟩
  have hloc : ∀ n : ℕ, MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) :=
    fun n => isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n
  have hmin : ∀ n : ℕ,
      minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).boundary ≠ 0 :=
    fun n => minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n) (hstepAll n)
  have hmono : ∀ n : ℕ, tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1)) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
    intro n
    have hit : monomialIterateFromEmpty hinv T (n + 1) =
        MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T n) :=
      MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n
    rw [hit]
    exact tripleAtLastBlowup_blowupAtCenter hinv T (monomialIterateFromEmpty hinv T n) (hstepAll n)
  have hdim : ∀ n : ℕ,
      krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).scheme ≤ T.krullDimSucc := by
    intro n
    induction n with
    | zero =>
      have h0 : monomialIterateFromEmpty hinv T 0 = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
        MarkedBlowupSequenceData.monomialBlowupIterate_zero hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
      have hsc : (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T 0)).scheme = T.scheme := by
        rw [tripleAtLastBlowup_scheme, h0, emptyMarkedBlowupSequenceData_schemeAt]
      exact le_of_eq (congrArg krullDimSucc hsc)
    | succ n ih =>
      rw [hmono n]
      exact le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom (hloc n) (hmin n)) ih
  have hdec : ∀ n : ℕ,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1))) <
        monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
    intro n
    have h' : minIndexCard (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).ideal
        (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).mult
        (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).boundary ≠ 0 := by
      rw [← hmono n]
      exact hmin (n + 1)
    rw [hmono n]
    exact monomialInvariant_blowupTripleAtCenterIdeal_lt hGeom (hloc n) (hmin n) (hdim n) h'
  have main : ∀ a : Lex (ℕ × Lex (ℕ × ℕ)), Acc (· < ·) a → ∀ n : ℕ,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) = a → False := by
    intro a ha
    induction ha with
    | intro x hx ih =>
      intro n hn
      refine ih (monomialInvariant T.krullDimSucc
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1)))) ?_ (n + 1) rfl
      rw [← hn]
      exact hdec n
  exact main (monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T 0)))
    (wellFounded_lt.apply _) 0 rfl

theorem minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).boundary = 0 := by
  by_contra hne
  have hstall := isStationaryAt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary
    (exists_isStationaryAt_emptyMarkedBlowupSequenceData hGeom hinv T hT)
  have hnot := (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
    (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (monomialStallIndexOfTriple hinv T)).mp hstall
  exact hnot (isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom T
    (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
      (monomialStallIndexOfTriple hinv T)) hne)

theorem monomialPrincipalization_length (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    (monomialPrincipalization hinv T).length = monomialStallIndexOfTriple hinv T := by
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_length, monomialBlowupSeq_length]

theorem monomialPrincipalization_length_eq_zero_of_empty (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0 := by
  intro T hT hcs
  have hmin : minIndexCard T.ideal T.mult T.boundary = 0 :=
    minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty hT.valid hcs
  have hT0 : tripleAtLastBlowup T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = T := by
    rw [tripleAtLastBlowup_eq_mk_of_length_eq T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) 0
      (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
    exact MarkedIdealWithBoundary.mk_eq_mk T.scheme T.mult (Category.id_comp T.structMap)
      (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
      (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
  have hns : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
    intro hstep
    have h := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hstep
    rw [hT0] at h
    exact h hmin
  have hzero : MarkedBlowupSequenceData.monomialStallIndex hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = 0 :=
    MarkedBlowupSequenceData.monomialStallIndex_eq_zero_of_not_isAdmissibleCenter hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hns
  rw [monomialPrincipalization_length]
  exact (monomialStallIndex_eq_monomialStallIndex_empty hinv T.structMap T.ideal T.mult T.boundary).trans hzero

theorem monomialPrincipalization_isResolution (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      MarkedSequenceOfBlowups.IsResolution (monomialPrincipalization hinv T) := by
  intro T hT
  have hmon : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))) :=
    isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT (monomialStallIndexOfTriple hinv T)
  have hzero := minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hcs := orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hGeom hmon hzero
  refine (MarkedSequenceOfBlowups.isResolution_iff _).mpr ?_
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_lastIdeal]
  exact hcs

private theorem support_comap_eqToHom_nonempty {A B : Scheme.{u}} (h : A = B)
    (J : B.IdealSheafData) (hJ : (J.support : Set ↥B).Nonempty) :
    ((J.comap (eqToHom h)).support : Set ↥A).Nonempty := by
  subst h
  obtain ⟨x, hx⟩ := hJ
  exact ⟨x, Scheme.IdealSheafData.mem_support_comap.mpr (by simpa using hx)⟩

theorem monomialPrincipalization_center_support_nonempty (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        (((monomialPrincipalization hinv T).center i).support :
          Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty := by
  intro T hT i hi
  rw [monomialPrincipalization_length] at hi
  have hlen : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hs := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i
  have hmin := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hlen
  have hne : ((monomialCenter (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).ideal
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).mult
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).boundary).support :
      Set ↥(tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).scheme).Nonempty := by
    rw [support_monomialCenter hGeom hs hmin]
    exact monomialCenterSet_nonempty hGeom hs hmin
  have hsupp : ((MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)).support :
      Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length)).Nonempty := hne
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_center,
    monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hlen]
  exact support_comap_eqToHom_nonempty
    (monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i (Nat.le_of_lt hlen))
    (MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)) hsupp

private theorem support_centerAtLast_subset_iUnion_boundary (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (i : ℕ) (hi : i < monomialStallIndexOfTriple hinv T) :
    ((MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)).support :
        Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length)) ⊆
      ⋃ D ∈ (monomialIterateFromEmpty hinv T i).boundary (monomialIterateFromEmpty hinv T i).length,
        ((D.support : Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length))) :=
  support_monomialCenter_subset_boundary hGeom
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i)
    (minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hi)

theorem monomialPrincipalization_center_subset_boundaryLocus (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        ↑((monomialPrincipalization hinv T).center i).support ⊆
          MarkedSequenceOfBlowups.boundaryLocus (monomialPrincipalization hinv T) i := by
  intro T hT i hi
  have hiN : i < monomialStallIndexOfTriple hinv T := by
    rwa [monomialPrincipalization_length] at hi
  have hcent := monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hbd := monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i (Nat.le_of_lt hiN)
  rw [monomialPrincipalization_apply]
  intro x hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_center, hcent] at hx
  refine (MarkedSequenceOfBlowups.mem_boundaryLocus_iff _ _ _).mpr ?_
  rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, hbd]
  obtain ⟨D, hD, hxD⟩ :=
    Set.mem_iUnion₂.mp
      (support_centerAtLast_subset_iUnion_boundary hGeom hinv T hT i hiN
        (Scheme.IdealSheafData.mem_support_comap.mp hx))
  exact ⟨_, List.mem_map.mpr ⟨D, hD, rfl⟩, Scheme.IdealSheafData.mem_support_comap.mpr hxD⟩

private theorem centerAtLast_eq_monomialCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData.centerAtLast d =
      monomialCenter (d.ideal d.length) m (d.boundary d.length) := rfl

private theorem monomialCenter_comap_eqToHom {X Y : Scheme.{u}} (h : X = Y)
    (J : Y.IdealSheafData) (m : ℕ) (E : List Y.IdealSheafData) :
    monomialCenter (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E) =
      (monomialCenter J m E).comap (eqToHom h) := by
  subst h
  simp

theorem monomialPrincipalization_center_eq_monomialCenter (_hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        (monomialPrincipalization hinv T).center i =
          monomialCenter ((monomialPrincipalization hinv T).ideal i) T.mult
            ((monomialPrincipalization hinv T).boundary i) := by
  intro T _ i hi
  rw [monomialPrincipalization_length hinv T] at hi
  have hi' : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hle : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := le_of_lt hi'
  have hobj := monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i hle
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_center,
    MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hi',
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hle,
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hle,
    centerAtLast_eq_monomialCenter]
  exact (monomialCenter_comap_eqToHom hobj _ T.mult _).symm

private theorem minIndexCard_comap_eqToHom {A B : Scheme.{u}} (h : A = B)
    (J : B.IdealSheafData) (m : ℕ) (E : List B.IdealSheafData) :
    minIndexCard (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E) =
      minIndexCard J m E := by
  subst h
  simp

theorem monomialPrincipalization_minIndexCard_ne_zero (_hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        minIndexCard ((monomialPrincipalization hinv T).ideal i) T.mult
          ((monomialPrincipalization hinv T).boundary i) ≠ 0 := by
  intro T _ i hi
  rw [monomialPrincipalization_length] at hi
  have hlt : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hle : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := Nat.le_of_lt hlt
  have hmin : minIndexCard
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).ideal
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) T.mult
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).boundary
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) ≠ 0 :=
    minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hlt
  have hEq := minIndexCard_comap_eqToHom
      (monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i hle)
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).ideal
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) T.mult
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).boundary
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length)
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_ideal,
    MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hle,
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hle]
  intro h0
  exact hmin (hEq.symm.trans h0)

private theorem isMonomialNear_comap_eqToHom {X Y : Scheme.{u}} (h : X = Y)
    (J : Y.IdealSheafData) (F : List Y.IdealSheafData) (m : ℕ)
    (hmon : ∀ y ∈ orderAtLeastLocus J m, MonomialCenter.IsMonomialNear F J y)
    (x : ↥X) (hx : x ∈ orderAtLeastLocus (J.comap (eqToHom h)) m) :
    MonomialCenter.IsMonomialNear (List.map (fun D => D.comap (eqToHom h)) F)
      (J.comap (eqToHom h)) x := by
  subst h
  have hx' : x ∈ orderAtLeastLocus J m := by simpa using hx
  simpa using hmon x hx'

theorem monomialPrincipalization_isMonomialNear (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i ≤ (monomialPrincipalization hinv T).length,
        ∀ x ∈ orderAtLeastLocus ((monomialPrincipalization hinv T).ideal i) T.mult,
          MonomialCenter.IsMonomialNear ((monomialPrincipalization hinv T).boundary i)
            ((monomialPrincipalization hinv T).ideal i) x := by
  intro T hT i hi
  have hiN : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := by
    rwa [monomialPrincipalization_length] at hi
  have hid := monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hbd := monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hmon : ∀ y ∈ orderAtLeastLocus ((monomialIterateFromEmpty hinv T i).ideal
        (monomialIterateFromEmpty hinv T i).length) T.mult,
      MonomialCenter.IsMonomialNear
        ((monomialIterateFromEmpty hinv T i).boundary (monomialIterateFromEmpty hinv T i).length)
        ((monomialIterateFromEmpty hinv T i).ideal (monomialIterateFromEmpty hinv T i).length) y :=
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i).monomialNear
  rw [monomialPrincipalization_apply]
  intro x hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_ideal, hid] at hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_boundary, hid, hbd]
  exact isMonomialNear_comap_eqToHom _ _ _ T.mult hmon x hx

theorem monomialPrincipalization_principalizationCertificate (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        PrincipalizationCertificate ((monomialPrincipalization hinv T).schemeAt i)
          (MarkedSequenceOfBlowups.projectionToSpec (monomialPrincipalization hinv T) i)
          ((monomialPrincipalization hinv T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (monomialPrincipalization hinv T) i)
          ((monomialPrincipalization hinv T).center i) := by
  intro T hT i hi
  exact PrincipalizationCertificate.memory
    (monomialPrincipalization_center_subset_boundaryLocus hGeom hinv T hT i hi)

private theorem centerInvariant_le_of_lt {n n' : ℕ} {a : MonomialCenter.CenterInvariant n} {b : MonomialCenter.CenterInvariant n'}
    (h : MonomialCenter.CenterInvariant.Lt a b) : MonomialCenter.CenterInvariant.Le a b := by
  unfold MonomialCenter.CenterInvariant.Le
  exact Or.inl h

private theorem comap_eqToHom_refl {A : Scheme.{u}} (h : A = A)
    (D : A.IdealSheafData) : D.comap (eqToHom h) = D := by
  rw [eqToHom_refl]
  simp

private theorem map_comap_eqToHom_refl {A : Scheme.{u}} (h : A = A)
    (E : List A.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h)) E = E := by
  induction E with
  | nil => rfl
  | cons _ _ _ => simp

private theorem centerInvariant_le_comap_eqToHom {A B A' B' : Scheme.{u}} (h : A = B) (h' : A' = B')
    (m : ℕ) (J : B.IdealSheafData) (E : List B.IdealSheafData)
    (J' : B'.IdealSheafData) (E' : List B'.IdealSheafData)
    (hle : MonomialCenter.CenterInvariant.Le (MonomialCenter.centerInvariant J m E) (MonomialCenter.centerInvariant J' m E')) :
    MonomialCenter.CenterInvariant.Le
      (MonomialCenter.centerInvariant (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E))
      (MonomialCenter.centerInvariant (J'.comap (eqToHom h')) m
        (List.map (fun D => D.comap (eqToHom h')) E')) := by
  subst h
  subst h'
  rw [map_comap_eqToHom_refl rfl E, map_comap_eqToHom_refl rfl E',
    comap_eqToHom_refl rfl J, comap_eqToHom_refl rfl J']
  exact hle

theorem monomialPrincipalization_centerInvariant_le_succ (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ t : ℕ, t + 1 < (monomialPrincipalization hinv T).length →
        (MonomialCenter.centerInvariant ((monomialPrincipalization hinv T).ideal t) T.mult
            ((monomialPrincipalization hinv T).boundary t)).Le
          (MonomialCenter.centerInvariant ((monomialPrincipalization hinv T).ideal (t + 1)) T.mult
            ((monomialPrincipalization hinv T).boundary (t + 1))) := by
  intro T hT t ht
  rw [monomialPrincipalization_length hinv T] at ht
  have ht1 : t + 1 < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := ht
  have ht0 : t < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary :=
    Nat.lt_of_succ_lt ht1
  have hstep : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T t) :=
    isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary t ht0
  have hiter : monomialIterateFromEmpty hinv T (t + 1) =
      MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T t) :=
    MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) t
  have hlastEq : tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1)) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)) := by
    rw [hiter]
    exact tripleAtLastBlowup_blowupAtCenter hinv T (monomialIterateFromEmpty hinv T t) hstep
  have hloc := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT t
  have hmin := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T t ht0
  have hmin1 := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T (t + 1) ht1
  have hdich := minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt hGeom hloc hmin
  rw [← hlastEq] at hdich
  have hlt : MonomialCenter.CenterInvariant.Lt
      (MonomialCenter.centerInvariant (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)).ideal T.mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)).boundary)
      (MonomialCenter.centerInvariant (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1))).ideal T.mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1))).boundary) := by
    rcases hdich with h | h
    · exact absurd h hmin1
    · exact h
  have hle := centerInvariant_le_of_lt hlt
  rw [monomialPrincipalization_apply,
    MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_ideal,
    MarkedBlowupSequenceData.toMarkedSequence_boundary, MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary t (Nat.le_of_lt ht0),
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary (t + 1) (Nat.le_of_lt ht1),
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary t (Nat.le_of_lt ht0),
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary (t + 1) (Nat.le_of_lt ht1)]
  exact centerInvariant_le_comap_eqToHom _ _ T.mult _ _ _ _ hle

structure IsMonomialCasePrincipalization (F : PrincipalizationAssignment.{u}) : Prop where
  center_subset_boundaryLocus :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        ↑((F T).center i).support ⊆ MarkedSequenceOfBlowups.boundaryLocus (F T) i
  cert :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        PrincipalizationCertificate ((F T).schemeAt i) (MarkedSequenceOfBlowups.projectionToSpec (F T) i) ((F T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (F T) i) ((F T).center i)
  center_eq :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        (F T).center i = monomialCenter ((F T).ideal i) T.mult ((F T).boundary i)
  minLevel_ne_zero :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length, minIndexCard ((F T).ideal i) T.mult ((F T).boundary i) ≠ 0
  key_le :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ t : ℕ, t + 1 < (F T).length →
        (MonomialCenter.centerInvariant ((F T).ideal t) T.mult ((F T).boundary t)).Le
          (MonomialCenter.centerInvariant ((F T).ideal (t + 1)) T.mult ((F T).boundary (t + 1)))
  monomial_near :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i ≤ (F T).length,
        ∀ x ∈ orderAtLeastLocus ((F T).ideal i) T.mult,
          MonomialCenter.IsMonomialNear ((F T).boundary i) ((F T).ideal i) x
  center_nonempty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length, (((F T).center i).support : Set ↥((F T).schemeAt i)).Nonempty
  resolves :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      MarkedSequenceOfBlowups.IsResolution (F T)
  trivial_of_coSupport_empty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      orderAtLeastLocus T.ideal T.mult = ∅ → (F T).length = 0

theorem isMonomialCasePrincipalization_monomialPrincipalization (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) : IsMonomialCasePrincipalization (monomialPrincipalization hinv) :=
  { center_subset_boundaryLocus :=
      monomialPrincipalization_center_subset_boundaryLocus hGeom hinv
    cert := monomialPrincipalization_principalizationCertificate hGeom hinv
    center_eq := monomialPrincipalization_center_eq_monomialCenter hGeom hinv
    minLevel_ne_zero := monomialPrincipalization_minIndexCard_ne_zero hGeom hinv
    key_le := monomialPrincipalization_centerInvariant_le_succ hGeom hinv
    monomial_near := monomialPrincipalization_isMonomialNear hGeom hinv
    center_nonempty := monomialPrincipalization_center_support_nonempty hGeom hinv
    resolves := monomialPrincipalization_isResolution hGeom hinv
    trivial_of_coSupport_empty := monomialPrincipalization_length_eq_zero_of_empty hinv }

end FunctorialResolution.EmbeddedResolution

end
