import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_comap_iso {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ) :
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom ⁻¹' orderAtLeastLocus J n :=
  orderAtLeastLocus_comap_iso_hom_eq_preimage e J n

namespace BlowupSequenceData

def iteratedStrictTransform {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) (D : X.IdealSheafData) :
    (d.obj i).IdealSheafData :=
  Nat.rec (motive := fun j => (d.obj j).IdealSheafData) (D.comap d.isoZero.hom)
    (fun j J => Blowup.strictTransform (d.map j) (d.center j) J) i

@[simp] theorem iteratedStrictTransform_zero {X : Scheme.{u}} (d : BlowupSequenceData X) (D : X.IdealSheafData) :
    d.iteratedStrictTransform 0 D = D.comap d.isoZero.hom := rfl

@[simp] theorem iteratedStrictTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ)
    (D : X.IdealSheafData) :
    d.iteratedStrictTransform (i + 1) D = Blowup.strictTransform (d.map i) (d.center i) (d.iteratedStrictTransform i D) := rfl

theorem boundary_cons {X : Scheme.{u}} (d : BlowupSequenceData X) (D : X.IdealSheafData)
    (L : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom (D :: L) i = d.iteratedStrictTransform i D :: d.boundaryFrom L i := by
  induction i with
  | zero => simp [BlowupSequenceData.boundary_zero]
  | succ i ih => simp [BlowupSequenceData.boundary_succ, ih]

theorem boundary_append {X : Scheme.{u}} (d : BlowupSequenceData X)
    (L₁ L₂ : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom (L₁ ++ L₂) i = L₁.map (d.iteratedStrictTransform i) ++ d.boundaryFrom L₂ i := by
  induction L₁ with
  | nil => simp
  | cons D L ih => simp [BlowupSequenceData.boundary_cons, ih]

end BlowupSequenceData

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal {Y Y' : Scheme.{u}} (π : Y' ⟶ Y)
    (J : Y.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π J) : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π J) := h.1

private theorem eq_of_exceptionalIdeal_pow_mul_eq (s : MarkedBlowupSequenceData p I m E) :
    ∀ i < s.length, ∀ A B : (s.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) → A = B := by
  intro i hi A B hA hB
  exact ((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.map i) (s.center i) (s.isBlowup i hi)).pow
    m).eq_of_mul_eq_mul (hA.trans hB.symm)

theorem controlledTransform_eq_ideal (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length) :
    s.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq_of_cancel (eq_of_exceptionalIdeal_pow_mul_eq s) i hi).1

theorem toBlowupSequenceData_boundary_eq (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length) :
    s.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      simp [BlowupSequenceData.boundary_zero, s.boundary_zero]
  | succ j ih =>
      intro hi
      have hj : j < s.length := hi
      rw [BlowupSequenceData.boundary_succ, ih (le_of_lt hj), s.boundary_succ j hj]

end MarkedBlowupSequenceData

private theorem foldr_lcm_consecutive_ne_zero (n : ℕ) :
    ∀ s : ℕ, s ≠ 0 → List.foldr Nat.lcm 1 (List.range' s n) ≠ 0 := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
      intro s hs
      have hr : List.range' s (n + 1) 1 = s :: List.range' (s + 1) n 1 := rfl
      rw [hr, List.foldr_cons]
      exact Nat.lcm_ne_zero hs (ih (s + 1) (by omega))

theorem one_le_tuningExponent (m : ℕ) : 1 ≤ tuningExponent m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have h1 : m ≤ 1 := by omega
    exact le_of_eq (tuningExponent_of_le_one h1).symm
  · have hl : lcmUpTo m ≠ 0 := by
      rw [lcmUpTo_eq_foldr]
      exact foldr_lcm_consecutive_ne_zero m 1 one_ne_zero
    have hm : m - 1 ≠ 0 := by omega
    have hne : tuningExponent m ≠ 0 := by
      rw [tuningExponent_of_two_le h]
      exact Nat.mul_ne_zero hm hl
    omega

namespace LowerDimReductionPullback

def tunedIdealAtLength (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    (s.obj s.length).IdealSheafData :=
  haveI := hft
  balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult

theorem tunedIdealAtLength_eq_balancedTunedSheaf (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    tunedIdealAtLength S s hft =
      haveI := hft
      balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult :=
  rfl

abbrev TunedMarkedBlowupSeq (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ) : Type (u + 1) :=
  MarkedSequenceOfBlowups (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft) (tuningExponent S.mult)
    (extra ++ (s.boundary s.length).drop ndrop)

private theorem tunedMarkedBlowupSeq_eq_derivedTriple_seq (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ) :
    TunedMarkedBlowupSeq S s hft extra ndrop = (MaxContactCoverData.derivedTriple S s hft extra ndrop).SequenceOfBlowups :=
  rfl

theorem structureMorphism_derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).structMap = s.proj s.length ≫ S.structMap :=
  MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop

theorem ideal_derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = tunedIdealAtLength S s hft :=
  rfl

theorem orderAt_ideal_length_le (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    ∀ x : ↥(s.obj s.length), orderAt (s.ideal s.length) x ≤ (S.mult : ℕ∞) := by
  have h := hstar.orderAt_level_le S hV hO s.toMarkedSequenceOfBlowups s.length
    (le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm)
  intro x
  exact h x

theorem maxOrderEq_ideal_length_of_nonempty (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty) :
    MaxOrderEq (s.ideal s.length) S.mult :=
  ⟨(orderLE_iff _ _).2 (orderAt_ideal_length_le hstar S hV hO s), hne⟩

theorem isOrderBoundedByMult_derivedTriple (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hm : 1 ≤ S.mult) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsOrderBoundedByMult := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have key : ∀ y : ↥(s.obj s.length),
      orderAt (tunedIdealAtLength S s hft) y ≤ ((tuningExponent S.mult : ℕ) : ℕ∞) := by
    by_cases hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅
    · have htuned : tunedIdealAtLength S s hft = ⊤ :=
        balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
          (s.ideal s.length) hm hempty
      intro y
      rw [htuned, orderAt_top]
      exact zero_le
    · have hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hempty
      have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
        maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
      have htune := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE S.base (s.obj s.length)
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult hm hmax
        (tuningExponent S.mult) (one_le_tuningExponent S.mult)
      have heq : tunedIdealAtLength S s hft =
          tunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
            (tuningExponent S.mult) :=
        balancedTunedSheaf_eq S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      intro y
      rw [heq]
      exact (orderLE_iff _ _).1 htune.2 y
  intro x
  rw [ideal_derivedTriple S s hft extra ndrop, MaxContactCoverData.derivedTriple_mult S s hft extra ndrop]
  exact key x

private theorem idealSheafData_top_pow {X : Scheme.{u}} (n : ℕ) :
    (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  have h1 : (1 : X.IdealSheafData) = ⊤ := by simp
  rw [← h1, one_pow]

theorem isBalanced_derivedTriple (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hm : 1 ≤ S.mult) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsBalanced hVc.locallyOfFiniteType := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have key : IsDerivBalanced S.base (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft)
      (tuningExponent S.mult) := by
    rcases Nat.lt_or_ge S.mult 2 with hlt | hge
    · have h1 : tuningExponent S.mult = 1 := tuningExponent_of_le_one (by omega)
      rw [h1]
      exact isDerivBalanced_one S.base (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft)
    · rcases Set.eq_empty_or_nonempty (orderAtLeastLocus (s.ideal s.length) S.mult) with hempty | hne
      · have htop : tunedIdealAtLength S s hft = ⊤ :=
          balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
            (s.ideal s.length) hm hempty
        rw [htop]
        refine isDerivBalanced_of_pow_le S.base (s.proj s.length ≫ S.structMap) ?_
        intro i _
        rw [idealSheafData_top_pow]
        exact le_top
      · have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
          maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
        have hexp : tuningExponent S.mult = (S.mult - 1) * lcmUpTo S.mult := tuningExponent_of_two_le hge
        have hderivPow := hstar.tuning.derivIdealSheafIter_tunedSheaf_pow_le
        unfold FunctorialResolution.EmbeddedResolution.IsDerivBalancedTunedSheafMulLcm at hderivPow
        have hderivPowAt := hderivPow S.base (s.obj s.length) (s.proj s.length ≫ S.structMap)
          (s.ideal s.length) S.mult hm hmax (S.mult - 1) le_rfl
        have hset : tunedIdealAtLength S s hft =
            tunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
              ((S.mult - 1) * lcmUpTo S.mult) := by
          rw [← hexp]
          exact balancedTunedSheaf_eq S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        refine isDerivBalanced_of_pow_le S.base (s.proj s.length ≫ S.structMap) ?_
        intro i hi
        rw [hexp] at hi
        rw [hset, hexp]
        exact hderivPowAt i hi
  exact key

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop) (j : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsBoundaryDivisorReduction P j A B)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop ndrop).length)
    (hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅) :
    (A (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length = 0 := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have htuned : tunedIdealAtLength S s hft = ⊤ :=
    balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) hm hempty
  have hjb : j < (MaxContactCoverData.derivedTriple S s hft extra ndrop).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary S s hft extra ndrop]
    exact hj
  have h1 : (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = ⊤ := by
    rw [ideal_derivedTriple S s hft extra ndrop]
    exact htuned
  have hcs : orderAtLeastLocus (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal
      (MaxContactCoverData.derivedTriple S s hft extra ndrop).mult = ∅ := by
    rw [h1, MaxContactCoverData.derivedTriple_mult S s hft extra ndrop]
    exact orderAtLeastLocus_top_eq_empty _ (one_le_tuningExponent S.mult)
  exact hspec.trivial_of_coSupport_empty _ hVc hP
    (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft extra ndrop hVc)
    (isBalanced_derivedTriple hstar S hV hm hO s hft extra ndrop hVc) hjb hcs

private theorem orderAtLeastLocus_controlledTransform_disjoint_strictTransform (hstar : MaxContactCoverProperties.{u}) {k : Type u}
    [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {d : BlowupSequenceData X} (hmk : d.IsMarked p I m E)
    (D : X.IdealSheafData) (hD : orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅) :
    ∀ i, i ≤ d.length →
      orderAtLeastLocus (d.controlledTransform I m i) m ∩ ((d.iteratedStrictTransform i D).support : Set ↥(d.obj i)) = ∅ := by
  intro i
  induction i with
  | zero =>
      intro _
      have hsupp : ((D.comap d.isoZero.hom).support : Set ↥(d.obj 0)) =
          ⇑d.isoZero.hom ⁻¹' (D.support : Set ↥X) := by
        rw [Scheme.IdealSheafData.support_comap]; rfl
      rw [BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero, orderAtLeastLocus_comap_iso,
        hsupp, ← Set.preimage_inter, hD, Set.preimage_empty]
  | succ i ih =>
      intro hi
      have hilt : i < d.length := hi
      have hih := ih (le_of_lt hilt)
      apply Set.eq_empty_of_subset_empty
      rintro x ⟨hx1, hx2⟩
      have heq := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ d I m i (hmk.divisible i hilt)
      have hsub := hstar.coSupport_le_preimage (d.map i) (d.center i) (d.isBlowup i hilt)
        (d.controlledTransform I m i) (d.controlledTransform I m (i + 1)) m heq (hmk.center_order i hilt)
      rw [BlowupSequenceData.iteratedStrictTransform_succ] at hx2
      have hmem : ⇑(d.map i) x ∈
          orderAtLeastLocus (d.controlledTransform I m i) m ∩ ((d.iteratedStrictTransform i D).support : Set ↥(d.obj i)) :=
        ⟨hsub hx1,
          support_strictTransform_subset_preimage (d.map i) (d.center i) (d.iteratedStrictTransform i D) hx2⟩
      rw [hih] at hmem
      simp at hmem

private theorem isMarked_append_of_orderAtLeastLocus_disjoint (hstar : MaxContactCoverProperties.{u}) {k : Type u} [Field k]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {L₁ L₃ : List X.IdealSheafData} (L₂ : List X.IdealSheafData) {d : BlowupSequenceData X}
    (hmk : d.IsMarked p I m (L₁ ++ L₃))
    (hsep : ∀ D ∈ L₂, orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅) :
    d.IsMarked p I m (L₂ ++ L₃) := by
  refine ⟨hmk.divisible, hmk.center_order, hmk.center_smooth, ?_⟩
  intro i hi
  have h1 := hmk.center_snc i hi
  rw [BlowupSequenceData.boundary_append] at h1
  rw [BlowupSequenceData.boundary_append]
  refine HasStrictNormalCrossingsWith.append_of_support_disjoint (HasStrictNormalCrossingsWith.of_append h1) ?_
  intro D hD
  obtain ⟨D0, hD0, hDeq⟩ := List.mem_map.mp hD
  subst hDeq
  have hdis := orderAtLeastLocus_controlledTransform_disjoint_strictTransform hstar hmk D0 (hsep D0 hD0) i (le_of_lt hi)
  apply Set.eq_empty_of_subset_empty
  rintro x ⟨hx1, hx2⟩
  have hx3 : x ∈ orderAtLeastLocus (d.controlledTransform I m i) m := hmk.center_order i hi hx2
  have hmem : x ∈ orderAtLeastLocus (d.controlledTransform I m i) m ∩
      ((d.iteratedStrictTransform i D0).support : Set ↥(d.obj i)) := ⟨hx3, hx1⟩
  rw [hdis] at hmem
  simp at hmem

private theorem isMarked_of_length_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (d : BlowupSequenceData X) (hd : d.length = 0) :
    d.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i hi
  all_goals rw [hd] at hi
  all_goals exact absurd hi (Nat.not_lt_zero i)

private theorem orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {J : X.IdealSheafData} {n : ℕ}
    {E : List X.IdealSheafData} (t : MarkedSequenceOfBlowups p J n E)
    (I : X.IdealSheafData) (m n' : ℕ) (hlen : t.toSequenceOfBlowups.length = 0)
    (hempty : orderAtLeastLocus I m = ∅) (hJ : J = ⊤) (hn1 : 1 ≤ n') :
    ∀ i ≤ t.toSequenceOfBlowups.length,
      orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
        orderAtLeastLocus (t.ideal i) n' := by
  have hJempty : orderAtLeastLocus J n' = ∅ := by
    rw [hJ]
    exact orderAtLeastLocus_top_eq_empty n' hn1
  intro i hi
  rw [hlen, Nat.le_zero] at hi
  subst hi
  have h1 : orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m 0) m = ∅ := by
    rw [BlowupSequenceData.controlledTransform_zero, orderAtLeastLocus_comap_iso, hempty, Set.preimage_empty]
  have h2 : orderAtLeastLocus (t.ideal 0) n' = ∅ := by
    rw [t.ideal_zero, orderAtLeastLocus_comap_iso, hJempty, Set.preimage_empty]
  exact h1.trans h2.symm

private theorem isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf (hstar : MaxContactCoverProperties.{u}) {k : Type u} [Field k]
    [CharZero k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) (hmax : MaxOrderEq I m)
    (L₁ L₂ L₃ E₀ : List X.IdealSheafData) (hE₀ : L₂ ++ L₃ = E₀)
    (hsep : ∀ D ∈ L₂, orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅)
    (t : MarkedSequenceOfBlowups p (balancedTunedSheaf k p I m) (tuningExponent m) (L₁ ++ L₃)) :
    ∃ _hmk : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p I m E₀,
      ∀ i ≤ t.toSequenceOfBlowups.length,
        orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
          orderAtLeastLocus (t.ideal i) (tuningExponent m) := by
  subst hE₀
  have hmarkedIff := hstar.tuning.isMarked_tuned_iff k X p I m hm hmax (L₁ ++ L₃)
    (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups)
  have hmkW : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p (balancedTunedSheaf k p I m) (tuningExponent m)
      (L₁ ++ L₃) := (MarkedBlowupSequenceData.ofMarkedSequence t).isMarked_toBlowupSequenceData
  have hmkI : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p I m (L₁ ++ L₃) := hmarkedIff.1.mpr hmkW
  refine ⟨isMarked_append_of_orderAtLeastLocus_disjoint hstar L₂ hmkI hsep, ?_⟩
  intro i hi
  have h2 := hmarkedIff.2.1 hmkI i (by rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact hi)
  have h3 : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform (balancedTunedSheaf k p I m) (tuningExponent m) i =
      t.ideal i :=
    MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq (MarkedBlowupSequenceData.ofMarkedSequence t) i
      (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact hi)
  exact h2.symm.trans (congrArg (fun Z => orderAtLeastLocus Z (tuningExponent m)) h3)

theorem appendLowerDimReduction_eq_append (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (reduce : (S' : MarkedIdealWithBoundary.{u}) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ (S' : MarkedIdealWithBoundary.{u}) (h : S'.krullDimSucc ≤ T.krullDimSucc) (i : ℕ), reduce S' h i = A i S')
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop ndrop).length)
    (hsep : ∀ D ∈ (s.boundary s.length).take ndrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅) :
    ∃ hmk :
        (BlowupSequenceData.ofSequenceOfBlowups
            (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).IsMarked
          (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length),
      MaxContactReduction.appendLowerDimReduction hinv T reduce S s extra ndrop j =
          s.append
            ((BlowupSequenceData.ofSequenceOfBlowups
                (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).toMarkedBlowupSequenceData
              (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
              (s.boundary s.length) hmk) hinv ∧
        ∀ i ≤ (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length,
          orderAtLeastLocus
              ((BlowupSequenceData.ofSequenceOfBlowups
                  (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).controlledTransform
                (s.ideal s.length) S.mult i) S.mult =
            orderAtLeastLocus ((A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).ideal i)
              (tuningExponent S.mult) := by
  have happend : MaxContactReduction.appendLowerDimReduction hinv T reduce S s extra ndrop j =
      MaxContactReduction.concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups) := by
    rw [MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T reduce S s extra ndrop j hft hdim,
      hrc (MaxContactCoverData.derivedTriple S s hft extra ndrop) hdim j]
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  by_cases hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅
  · have hlen : (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P j (A j) B hspec S hV hm hO s hft extra ndrop hP hVc hj hempty
    have hJtop : (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = ⊤ := by
      rw [ideal_derivedTriple S s hft extra ndrop]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) hm hempty
    have hmk : (BlowupSequenceData.ofSequenceOfBlowups
        (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).IsMarked
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) :=
      isMarked_of_length_eq_zero (s.proj s.length ≫ S.structMap) (s.ideal s.length)
        S.mult (s.boundary s.length) _ ((BlowupSequenceData.ofSequenceOfBlowups_length _).trans hlen)
    exact ⟨hmk, happend.trans (MaxContactCoverData.concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk),
      orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero
        (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop))
        (s.ideal s.length) S.mult (tuningExponent S.mult) hlen hempty hJtop
        (one_le_tuningExponent S.mult)⟩
  · have hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
      maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
    obtain ⟨hmk, hcos⟩ := isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf hstar (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult hm hmax extra ((s.boundary s.length).take ndrop)
      ((s.boundary s.length).drop ndrop) (s.boundary s.length)
      (List.take_append_drop ndrop (s.boundary s.length)) hsep
      (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop))
    exact ⟨hmk, happend.trans (MaxContactCoverData.concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk), hcos⟩

end LowerDimReductionPullback

end FunctorialResolution.EmbeddedResolution

end
