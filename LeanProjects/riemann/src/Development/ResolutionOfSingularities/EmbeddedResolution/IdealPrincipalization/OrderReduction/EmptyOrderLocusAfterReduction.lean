import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
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
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BoundarySeparationByMaxContact

private theorem orderAtLeastLocus_eq_support_maxContactIdeal (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus A m = ((maxContactIdeal k p A m).support : Set ↥P) := by
  have hlt : m - 1 < m := by omega
  have hd := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega] at hd
  ext x
  rw [← hd]
  exact mem_orderAtLeastLocus_one_iff _ x

private theorem restrictIdeal_eq_comap {X : Scheme.{u}} (D : X.IdealSheafData) (V : X.Opens) :
    restrictIdeal D V = D.comap V.ι := rfl

private theorem mem_support_toBlowupSequenceData_iteratedStrictTransform {k : Type u} [Field k]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ)
    (x : ↥(s.obj i))
    (hx : x ∈ ((MaxContactReduction.iteratedStrictTransform s H i).support : Set ↥(s.obj i))) :
    x ∈ ((s.toBlowupSequenceData.iteratedStrictTransform i H).support : Set ↥(s.obj i)) := by
  rw [← iteratedStrictTransform_eq_toBlowupSequenceData s H i]
  exact hx

private theorem orderAtLeastLocus_subset_support_of_isMaxContactHypersurface (k : Type u) [Field k]
    [CharZero k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    (A H : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hH : IsMaxContactHypersurface k p A μ H) :
    orderAtLeastLocus A μ ⊆ (H.support : Set ↥P) := by
  intro x hx
  obtain ⟨U, _, hxU, hcase⟩ := hH x
  rcases hcase with ⟨hdisj, _⟩ | ⟨_, _, _, hcoord, hmcc⟩
  · exact absurd hxU (Set.disjoint_left.1 hdisj hx)
  · have hmc : x ∈ ((maxContactIdeal k p A μ).support : Set ↥P) := by
      rw [← orderAtLeastLocus_eq_support_maxContactIdeal k p A μ hμ]
      exact hx
    have hbase : (U.ι).base (⟨x, hxU⟩ : ↥U) = x := rfl
    have h1 : (⟨x, hxU⟩ : ↥U) ∈ ((maxContactIdeal k p A μ).comap U.ι).support := by
      refine AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 ?_
      rw [hbase]
      exact hmc
    have hle : (H.comap U.ι) ≤ ((maxContactIdeal k p A μ).comap U.ι) := by
      rw [← restrictIdeal_eq_comap, ← restrictIdeal_eq_comap, hcoord]
      exact hmcc
    have h2 : (⟨x, hxU⟩ : ↥U) ∈ (H.comap U.ι).support :=
      Scheme.IdealSheafData.support_antitone hle h1
    have h3 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 h2
    rw [hbase] at h3
    exact h3

private theorem orderAtLeastLocus_comap_iso_eq_empty {X Y : Scheme.{u}} (e : X ≅ Y)
    (J : Y.IdealSheafData) (n : ℕ) (hJ : orderAtLeastLocus J n = ∅) :
    orderAtLeastLocus (J.comap e.hom) n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n, hJ, Set.preimage_empty]

private theorem orderAtLeastLocus_eq_empty_of_comap_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (J : Y.IdealSheafData) (n : ℕ) (hJ : orderAtLeastLocus (J.comap e.hom) n = ∅) :
    orderAtLeastLocus J n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n] at hJ
  have hsurj : ∀ y : ↥Y, ∃ x : ↥X, e.hom x = y := by
    intro y
    refine ⟨e.inv y, ?_⟩
    simp
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨x, hx⟩ := hsurj y
  have hmem : x ∈ (⇑e.hom ⁻¹' orderAtLeastLocus J n) := by
    simp only [Set.mem_preimage, hx]
    exact hy
  rw [hJ] at hmem
  exact hmem

private theorem orderAtLeastLocus_append_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (ht : ∀ i : ℕ, i = t.length → orderAtLeastLocus (t.ideal i) n = ∅)
    (hs : t.length = 0 → ∀ i : ℕ, i = s.length → orderAtLeastLocus (s.ideal i) n = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) n = ∅ := by
  have key : ∀ i : ℕ, i = s.length + t.length →
      orderAtLeastLocus ((s.append t hinv).ideal i) n = ∅ := by
    rintro i rfl
    rw [MarkedBlowupSequenceData.append_ideal]
    rcases Nat.eq_zero_or_pos t.length with hz | hpos
    · have hle : s.length + t.length ≤ s.length := by omega
      have hobj : (s.appendToBlowupSequenceData t).obj (s.length + t.length) = s.obj (s.length + t.length) :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s t hle
      rw [MarkedBlowupSequenceData.appendIdeal_of_le_length s t hle]
      exact orderAtLeastLocus_comap_iso_eq_empty (eqToIso hobj) _ _ (hs hz _ (by omega))
    · have hgt : s.length < s.length + t.length := by omega
      have hobj : (s.appendToBlowupSequenceData t).obj (s.length + t.length)
          = t.obj (s.length + t.length - s.length) :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt
      rw [MarkedBlowupSequenceData.appendIdeal_of_length_lt s t hgt]
      exact orderAtLeastLocus_comap_iso_eq_empty (eqToIso hobj) _ _ (ht _ (by omega))
  exact key _ (MarkedBlowupSequenceData.append_length s t hinv)

private theorem orderAtLeastLocus_derivedTriple_ideal_length_eq_empty (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible) (hmS : 1 ≤ S.mult)
    (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap))
    (Hc : (s.obj s.length).IdealSheafData)
    (hHc : @IsMaxContactHypersurface S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (s.ideal s.length) S.mult Hc)
    (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsAdmissible)
    (hPdim : P (MaxContactCoverData.derivedTriple S s hft [Hc] keep).krullDimSucc)
    (hN : ∀ i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.length,
        AlgebraicGeometry.IsLocallyNoetherian
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.obj i)) :
    ∀ i : ℕ, i = (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length →
      orderAtLeastLocus ((A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).ideal i)
        (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult = ∅ := by
  rintro i rfl
  have := hft
  have := hsm
  have : CharZero S.base := hSV.charZero
  have hOB : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc
  have hbalanced : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsBalanced hVc.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc
  have hj : 0 < (MaxContactCoverData.derivedTriple S s hft [Hc] keep).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  obtain ⟨Dv, bv, _, hDvEq, _, hBoundaryOfMem, hBoundaryOfLt, hBoundaryEq, _⟩ :=
    (hspec 0).shape (MaxContactCoverData.derivedTriple S s hft [Hc] keep) hVc hPdim hOB hbalanced hj
  have htuned : @IsMaxContactHypersurface S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) Hc :=
    isMaxContactHypersurface_balancedTunedSheaf hstar S.base (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult hmS (LowerDimReductionPullback.orderAt_ideal_length_le hstar S hSV hSO s) Hc hHc
  have hadm2 : @IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base _
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).scheme
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap hVc.locallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult Hc := by
    rw [MaxContactCoverData.derivedTriple_mult]
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap)
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap hft hVc.locallyOfFiniteType
      (LowerDimReductionPullback.tunedIdealAtLength S s hft) (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal Hc Hc
      (tuningExponent S.mult)
      (MaxContactCoverData.derivedTriple_structureMorphism S s hft [Hc] keep).symm
      (LowerDimReductionPullback.ideal_derivedTriple S s hft [Hc] keep).symm rfl htuned
  have hordT : ∀ x : ↥(MaxContactCoverData.derivedTriple S s hft [Hc] keep).scheme,
      orderAt (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal x
        ≤ (((MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult : ℕ) : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).1 hOB
  have : CharZero (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base := hVc.charZero
  have hftL := locallyOfFiniteType_projectionToBase_comp hstar (MaxContactCoverData.derivedTriple S s hft [Hc] keep)
    hVc (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hsmL := smooth_projectionToBase_comp hstar (MaxContactCoverData.derivedTriple S s hft [Hc] keep)
    hVc (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hadmL := isMaxContactHypersurface_iteratedStrictTransform hstar
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep) hVc hordT Hc hadm2
    (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hsub1 := @orderAtLeastLocus_subset_support_of_isMaxContactHypersurface
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base _ _ _
    ((MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).proj
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length ≫
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap) hsmL hftL
    ((MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).ideal
      (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length)
    (MaxContactReduction.iteratedStrictTransform
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))) Hc
      (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length)
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult hVc.one_le_mult hadmL
  have h0 : Dv 0 = Hc.comap (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.isoZero.hom := by
    rw [hDvEq]
    rfl
  have hstep : ∀ tt : ℕ, tt < (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.length →
      Dv (tt + 1) = Blowup.strictTransform
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.map tt)
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.center tt) (Dv tt) ∨
        Dv (tt + 1) = (Dv tt).comap
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.map tt) := by
    intro tt htt
    by_cases hb : bv = true ∧ tt = 0
    · obtain ⟨hb1, hb2⟩ := hb
      subst hb2
      exact Or.inr (hBoundaryOfMem hb1).2.2
    · exact Or.inl (hBoundaryOfLt tt htt hb)
  have hsub2raw := BlowupSequenceData.support_iteratedStrictTransform_subset_support
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData hN Hc Dv h0 hstep
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hx2 := mem_support_toBlowupSequenceData_iteratedStrictTransform _ _ _ _ (hsub1 hx)
  have hmem : x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.lastIdeal
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
        (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult ∩
      (((Dv (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length).support) :
        Set ↥((A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).schemeAt
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length)) :=
    ⟨hx, hsub2raw hx2⟩
  rw [hBoundaryEq] at hmem
  exact hmem

theorem orderAtLeastLocus_coverMarkedBlowupData_eq_empty (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    orderAtLeastLocus
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).ideal
          (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length)
        (MaxContactCoverData.tunedMult T) = ∅ := by
  obtain ⟨hft, hVc, hPdim, hmk, heq, hcs⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hScV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hScO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hsmS : AlgebraicGeometry.Smooth
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    smooth_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hScV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hadm0 : @IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base _
      ((separateAllBoundary T h.valid hinv A).obj (separateAllBoundary T h.valid hinv A).length)
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) hft
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_iteratedStrictTransform hstar (MaxContactCoverData.coverTriple T h.valid) hScV hScO
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hNo : ∀ i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData.length,
      AlgebraicGeometry.IsLocallyNoetherian
        ((MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData.obj i) := by
    intro i hi
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar (MaxContactCoverData.coverTriple T h.valid) hScV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i hi
  have hlow := orderAtLeastLocus_derivedTriple_ideal_length_eq_empty hstar P A B hspec
    (MaxContactCoverData.coverTriple T h.valid) hScV hScV.one_le_mult hScO
    (separateAllBoundary T h.valid hinv A) hft hsmS
    (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hadm0
    (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc hPdim hNo
  rw [heq, ← MaxContactCoverData.coverTriple_mult T h.valid]
  refine orderAtLeastLocus_append_eq_empty (separateAllBoundary T h.valid hinv A)
    (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv
    (MaxContactCoverData.coverTriple T h.valid).mult ?_ ?_
  · rintro i rfl
    refine Eq.trans (hcs (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups.length
      (le_refl _)) ?_
    rw [← MaxContactCoverData.derivedTriple_mult (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length]
    exact hlow _ rfl
  · intro hz i hi
    subst hi
    refine orderAtLeastLocus_eq_empty_of_comap_iso
      (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).isoZero
      _ _ ?_
    refine Eq.trans (hcs 0 (Nat.zero_le _)) ?_
    rw [← MaxContactCoverData.derivedTriple_mult (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length]
    exact hlow 0 hz.symm

private theorem comap_ne_top_of_surjective_base {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : ∀ x : ↥X, ∃ y : ↥Y, f.base y = x) (J : X.IdealSheafData) (hJ : J ≠ ⊤) :
    J.comap f ≠ ⊤ := by
  intro htop
  refine hJ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty J).2 ?_)
  have h0 : ((J.comap f).support : Set ↥Y) = ∅ :=
    (Scheme.IdealSheafData.eq_top_iff_support_eq_empty (J.comap f)).1 htop
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, hy⟩ := hf x
  have h1 : (1 : ℕ∞) ≤ orderAt J (f.base y) := by
    rw [hy]
    exact (one_le_orderAt_iff_mem_support J x).2 hx
  have h2 : y ∈ ((J.comap f).support : Set ↥Y) :=
    (one_le_orderAt_iff_mem_support (J.comap f) y).1
      (le_trans h1 (orderAt_le_orderAt_comap f J y))
  rw [h0] at h2
  exact (Set.mem_empty_iff_false y).1 h2

private theorem exists_base_eqToHom_eq {X Y : Scheme.{u}} (h : X = Y) (x : ↥Y) :
    ∃ y : ↥X, (CategoryTheory.eqToHom h).base y = x := by
  subst h
  refine ⟨x, ?_⟩
  simp

private theorem exists_base_iso_inv_eq {X Y : Scheme.{u}} (e : X ≅ Y) (x : ↥X) :
    ∃ y : ↥Y, e.inv.base y = x :=
  ⟨e.hom.base x, congrArg (fun f : X ⟶ X => f.base x) e.hom_inv_id⟩

private theorem length_pos_of_eq_cons {α : Type*} {L : List α} {a : α} {M : List α}
    (h : L = a :: M) : 0 < L.length := by
  subst h
  exact Nat.succ_pos _

private theorem center_append_ne_top {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u})
    (hs : ∀ i < s.length, s.center i ≠ ⊤)
    (ht : ∀ i < t.length, t.center i ≠ ⊤) :
    ∀ i < (s.append t hinv).length, (s.append t hinv).center i ≠ ⊤ := by
  intro i hi
  rw [MarkedBlowupSequenceData.append_length] at hi
  rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
  rcases lt_trichotomy i s.length with hlt | hmid | hgt
  · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length s t hlt]
    exact comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ (hs i hlt)
  · subst hmid
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s t]
    refine comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ ?_
    refine comap_ne_top_of_surjective_base _ (exists_base_iso_inv_eq _) _ ?_
    exact ht 0 (by omega)
  · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s t hgt]
    exact comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ (ht _ (by omega))

theorem center_coverMarkedBlowupData_ne_top (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∀ i < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length,
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).center i
        ≠ ⊤ := by
  obtain ⟨hft, hVc, hP, hmk, heq, _⟩ :=
    exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hOB : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      hV.one_le_mult hO (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
  have hbalanced : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsBalanced hVc.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      hV.one_le_mult hO (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
  have hb : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary =
      MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid) ::
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length).drop
            (MaxContactCoverData.coverTriple T h.valid).boundary.length :=
    MaxContactCoverData.derivedTriple_boundary (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
  have hbd : 0 < (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.length :=
    length_pos_of_eq_cons hb
  have hcn := (hspec 0).center_nonempty (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hVc hP hOB hbalanced hbd
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    (MaxContactCoverData.coverTriple T h.valid).boundary.length (le_refl _)
  rw [heq]
  refine center_append_ne_top _ _ _ (And.left (And.right hfacts)) ?_
  intro i hi htop
  have hi' : i < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length := hi
  exact (hcn i hi').ne_empty
    ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).1 htop)

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
