import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

structure MaxContactCoverProperties : Prop where
  strictTransform_admissible :
    ∀ (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}}
      (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.IsLocallyNoetherian P₁]
      (π : P₁ ⟶ P) [AlgebraicGeometry.LocallyOfFiniteType (π ≫ p)]
      (Z : P.IdealSheafData) (E : List P.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ), 1 ≤ μ →
        (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
        (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ →
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
          IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H)
  coSupport_le_preimage :
    ∀ {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData) (μ : ℕ),
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ →
        orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ
  schemeDim_level_le :
    ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  exists_goodCover :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
        MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType
          (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  hasSNCWith_cons :
    ∀ (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] (Z H : P.IdealSheafData) (N : List P.IdealSheafData),
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
      InStrictNormalCrossingPosition p (H :: N) → HasStrictNormalCrossingsWith p Z N → H ≤ Z →
      HasStrictNormalCrossingsWith p Z (H :: N)
  valid_level :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      (T.transformAt s i).IsAdmissible
  orderAt_level_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
        ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  coverTriple_dim_le :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc
  coverTriple_valid :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      (MaxContactCoverData.coverTriple T hv).IsAdmissible
  coverContact_admissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      ∀ [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T)
          (MaxContactCoverData.coverMaxContactIdeal T hv)
  coverContact_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
        [MaxContactCoverData.coverMaxContactIdeal T hv]
  tuning : TunedSheafProperties.{u}

theorem MaxContactCoverProperties.krullDimSucc_schemeAt_le_dim (hf : MaxContactCoverProperties.{u}) {S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    krullDimSucc (s.obj i) ≤ S.krullDimSucc :=
  hf.schemeDim_level_le S hv s.toMarkedSequenceOfBlowups i (by simpa using hi)

theorem MaxContactCoverProperties.derivedTriple_dim_le (hf : MaxContactCoverProperties.{u}) {T S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hdim : S.krullDimSucc ≤ T.krullDimSucc) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc :=
  le_trans (hf.krullDimSucc_schemeAt_le_dim hv s s.length le_rfl) hdim

private theorem isMaxContactHypersurface_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p q : X ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.LocallyOfFiniteType q] (h : p = q) {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (hH : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface k q A m H := by
  subst h
  exact hH

theorem MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i)]
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec (i + 1))]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hH : IsMaxContactHypersurface T.base (s.projectionToSpec i) (s.ideal i) T.mult H) :
    IsMaxContactHypersurface T.base (s.projectionToSpec (i + 1)) (s.ideal (i + 1)) T.mult
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) H) := by
  have hi' : i ≤ s.toSequenceOfBlowups.length := le_of_lt hi
  have hvi := hf.valid_level T hv s i hi'
  have hvi1 := hf.valid_level T hv s (i + 1) hi
  have : CharZero T.base := hv.charZero
  have : AlgebraicGeometry.Smooth (s.projectionToSpec i) := hvi.smooth
  have hno : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := hvi1.isNoetherian
  have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := inferInstance
  have : AlgebraicGeometry.LocallyOfFiniteType
      (s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i) := by
    rw [← MarkedSequenceOfBlowups.projectionToSpec_succ]
    infer_instance
  have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have key := hf.strictTransform_admissible T.base (s.projectionToSpec i)
    (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) (s.boundary i) hsnc
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) (s.ideal (i + 1)) T.mult
    hv.one_le_mult (hf.orderAt_level_le T hv hord s i hi') (s.center_order i hi)
    (s.ideal_succ i hi) H hH
  exact isMaxContactHypersurface_of_eq (MarkedSequenceOfBlowups.projectionToSpec_succ s i).symm key

theorem MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.Smooth (s.projectionToSpec i)]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (N : List (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hsnc : InStrictNormalCrossingPosition (s.projectionToSpec i) (H :: N))
    (hZN : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) N)
    (hHZ : H ≤ s.toSequenceOfBlowups.center i) :
    HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (H :: N) := by
  have hsm : AlgebraicGeometry.Smooth
      ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_smooth i hi
  exact hf.hasSNCWith_cons T.base (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) H N hsm hsnc hZN hHZ

end FunctorialResolution.EmbeddedResolution
