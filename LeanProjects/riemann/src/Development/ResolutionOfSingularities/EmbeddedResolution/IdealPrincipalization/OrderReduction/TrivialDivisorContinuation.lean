import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace TrivialDivisorContinuation

private theorem hom_apply_congr {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (x : ↥A) : f x = g x := by
  subst h; rfl

private theorem mem_support_of_eq {A : Scheme.{u}} {M : A.IdealSheafData} {x y : ↥A} (h : x = y)
    (hx : y ∈ M.support) : x ∈ M.support := by
  subst h; exact hx

private theorem projectionToBase_zero_isoObjZero_inv_apply {W : Scheme.{u}} (n : FunctorialResolution.EmbeddedResolution.BlowupSequenceData W) (w : ↥W) :
    (n.projectionToBase 0) (n.isoZero.inv w) = w :=
  (hom_apply_congr (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_zero n) (n.isoZero.inv w)).trans
    (Scheme.inv_hom_apply n.isoZero w)

private theorem notMem_support_of_eq_top {A : Scheme.{u}} {M : A.IdealSheafData} (h : M = ⊤)
    (x : ↥A) : x ∉ M.support := by
  have h2 : (↑M.support : Set ↥A) = ∅ :=
    (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty M).mp h
  intro hx
  have hx' : x ∈ (↑M.support : Set ↥A) := hx
  rw [h2] at hx'
  exact hx'

private theorem false_of_mem_support_comp {X' Y W Z : Scheme.{u}} (q : X' ⟶ Y) (pr : W ⟶ Y)
    (M : W.IdealSheafData)
    (hImageDisjoint : ∀ y : ↥W, y ∈ M.support → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ pr) z)
    (hz : g z ∈ M.support) : False :=
  hImageDisjoint (g z) hz x hx

private theorem false_of_mem_support_comp_comp {X' Y W Z Z' : Scheme.{u}} (q : X' ⟶ Y)
    (pr : W ⟶ Y) (M : W.IdealSheafData)
    (hImageDisjoint : ∀ y : ↥W, y ∈ M.support → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ Z') (h : Z' ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ (h ≫ pr)) z)
    (hz : h (g z) ∈ M.support) : False :=
  hImageDisjoint (h (g z)) hz x hx

theorem nonempty_pullback_appendLowerDimReduction_of_comap_eq_top
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (j₁ : ℕ)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
    (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hstar : MaxContactCoverProperties.{u}) (hspec : IsBoundaryDivisorReduction P j₁ (A j₁) B)
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hP : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible)
    (hj : j₁ < (s.boundary s.length).length)
    (hComapTop : ((s.boundary s.length).get ⟨j₁, hj⟩).comap D.lastMap = ⊤)
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hdim : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc) :
    Nonempty (SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [] 0
        j₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  set Dj := (s.boundary s.length).get ⟨j₁, hj⟩ with hDtopDef
  have hmapeq : s.toMarkedSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.length = s.toBlowupSequenceData.projectionToBase s.length :=
    FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups_projectionToBase s.toBlowupSequenceData s.length
  have hImageDisjoint : ∀ y : ↥(s.obj s.length), y ∈ Dj.support →
      ∀ x'' : ↥X', q x'' ≠ (s.toBlowupSequenceData.projectionToBase s.length) y := by
    intro y hy x'' hxy
    have hpb := D.isPullback_lastMap
    have hcomm : (s.toMarkedSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.length) y = q x'' :=
      (hom_apply_congr hmapeq y).trans hxy.symm
    obtain ⟨w, hw1, -⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback y x'' hcomm
    have h1 : D.lastMap (hpb.isoPullback.inv w) = y :=
      (hom_apply_congr hpb.isoPullback_inv_fst w).trans hw1
    have h4 : (hpb.isoPullback.inv w) ∈ (Dj.comap D.lastMap).support :=
      Scheme.IdealSheafData.mem_support_comap.mpr (mem_support_of_eq h1 hy)
    exact notMem_support_of_eq_top hComapTop _ h4
  have hb : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple_boundary]
    simp
  have hj' : j₁ < (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [hb]; exact hj
  have hget : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j₁, hj'⟩ = Dj := by
    rw [hDtopDef]
    have hgen : ∀ (L L' : List (s.obj s.length).IdealSheafData), L = L' →
        ∀ (h1 : j₁ < L.length) (h2 : j₁ < L'.length), L.get ⟨j₁, h1⟩ = L'.get ⟨j₁, h2⟩ := by
      rintro L L' rfl h1 h2
      rfl
    exact hgen _ _ hb hj' hj
  have hOB := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbalanced := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  obtain ⟨Dv, bb, -, hD0, hcen, hbtrue, hstrictD, -, -⟩ :=
    hspec.shape (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0) hVc hP hOB hbalanced hj'
  have hInduction : ∀ r : ℕ,
      r ≤ (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length →
      ∀ z : ↥((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).schemeAt r),
        z ∈ (Dv r).support →
        ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).projectionToBase r) z
          ∈ Dj.support := by
    intro r
    induction r with
    | zero =>
      intro _ z hz
      rw [hD0, hget] at hz
      exact mem_support_of_eq (hom_apply_congr (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero _) z)
        (Scheme.IdealSheafData.mem_support_comap.mp hz)
    | succ r ih =>
      intro hr z hz
      have hrlt : r < (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length := hr
      have hmem : ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc r) z
          ∈ (Dv r).support := by
        by_cases hc : bb = true ∧ r = 0
        · obtain ⟨hb1, hb2⟩ := hc
          subst hb2
          obtain ⟨-, -, hD1⟩ := hbtrue hb1
          have hz' : z ∈ (Dv 1).support := hz
          rw [hD1] at hz'
          exact Scheme.IdealSheafData.mem_support_comap.mp hz'
        · rw [hstrictD r hrlt hc] at hz
          exact FunctorialResolution.EmbeddedResolution.support_strictTransform_subset_preimage _ _ _ hz
      have hnext := ih (le_of_lt hrlt) _ hmem
      exact mem_support_of_eq (hom_apply_congr (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ _ r) z) hnext
  have hcent : ∀ nn : FunctorialResolution.EmbeddedResolution.BlowupSequenceData (s.obj s.length),
      nn = FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups
        (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups →
      ∀ (r : ℕ) (z : ↥(nn.obj r)), z ∈ (nn.center r).support → r < nn.length →
        (nn.projectionToBase r) z ∈ Dj.support := by
    rintro nn rfl r z hz hr
    have hr' : r < (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length := hr
    have hz2 : z ∈ ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).center r).support :=
      hz
    have hmem := hInduction r (le_of_lt hr') z (hcen r hr' hz2)
    exact mem_support_of_eq (hom_apply_congr (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
      (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups r) z) hmem
  have c : FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback q s'.toSequenceOfBlowups s.toSequenceOfBlowups := by
    rw [← FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s,
        ← FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s']
    exact D
  have hcd : ∀ (tt : FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult (s.boundary s.length)),
      (s.append tt hinv).toSequenceOfBlowups = (s.toBlowupSequenceData.append tt.toBlowupSequenceData).toSequenceOfBlowups := fun tt =>
    congrArg FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups
      ((FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.append_toBlowupSequenceData s tt hinv).trans rfl)
  have main : ∀ (tt : FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) S.mult (s.boundary s.length)),
      tt.toBlowupSequenceData = FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups
        (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups →
      Nonempty (FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (s.append tt hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro tt htt
    have hcn := hcent tt.toBlowupSequenceData htt
    rw [FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s',
        FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (s.append tt hinv), hcd tt]
    refine FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers q s'.toBlowupSequenceData s.toBlowupSequenceData
      tt.toBlowupSequenceData c ?_
    intro i hi1 hi2 z hz x'' hx
    rcases eq_or_lt_of_le hi1 with he | hlt
    · subst he
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.append_center_length] at hz
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_append_of_le_length _ _ (le_refl _)] at hx
      have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
      have hz2 := Scheme.IdealSheafData.mem_support_comap.mp hz1
      have hy := hcn 0 _ hz2 (by omega)
      exact false_of_mem_support_comp q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _ z x'' hx
        (mem_support_of_eq (projectionToBase_zero_isoObjZero_inv_apply _ _).symm hy)
    · rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.append_center_of_length_lt _ _ hlt] at hz
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_append_of_length_lt _ _ hlt] at hx
      have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
      have hy := hcn (i - s.toBlowupSequenceData.length) _ hz1 (by omega)
      exact false_of_mem_support_comp_comp q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _
        (tt.toBlowupSequenceData.projectionToBase (i - s.toBlowupSequenceData.length)) z x'' hx hy
  obtain ⟨hmk, heq, -⟩ := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j₁ hspec
      (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdim hP hVc
      (by simpa using hj) (fun Dx hDx => FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S s Dx hDx)
  rw [heq]
  exact main _ (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toMarkedBlowupSequenceData_toBlowupSequenceData _ _ _ _ _ _)

end TrivialDivisorContinuation

end FunctorialResolution.EmbeddedResolution

end
