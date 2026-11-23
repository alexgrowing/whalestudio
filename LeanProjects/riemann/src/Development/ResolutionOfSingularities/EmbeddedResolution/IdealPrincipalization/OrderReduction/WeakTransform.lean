import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def MaxContactIdealComapLeControlled : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X₁ : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ [AlgebraicGeometry.IsLocallyNoetherian X₁] [AlgebraicGeometry.Smooth (π ≫ p)]
        [AlgebraicGeometry.LocallyOfFiniteType (π ≫ p)]
        (A : X.IdealSheafData) (μ : ℕ), 1 ≤ μ → A ≤ Z ^ μ →
      ∀ A₁ : X₁.IdealSheafData,
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (maxContactIdeal k p A μ).comap π ≤
          Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ

theorem smooth_projectionToBase_comp {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.Smooth q] {A : V.IdealSheafData}
    {μ : ℕ} {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E) (i : ℕ)
    (hi : i ≤ u.length) : AlgebraicGeometry.Smooth (u.projectionToBase i ≫ q) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have h0 : u.projectionToBase 0 ≫ q = u.isoZero.hom ≫ q := by
      rw [SequenceOfBlowups.projectionToBase_zero]
    rw [h0]
    infer_instance
  | succ j ih =>
    intro hj1
    have hj : j < u.length := hj1
    have := ih hj.le
    have hsucc : u.projectionToBase (j + 1) ≫ q = u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q) := by
      rw [SequenceOfBlowups.projectionToBase_succ, Category.assoc]
    rw [hsucc]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (u.center_snc j hj) (u.isBlowupAlongIdealSheaf_blowupMorphism j hj)

private theorem le_pow_one_of_le {X : Scheme.{u}} {b Z : X.IdealSheafData} (h : b ≤ Z) :
    b ≤ Z ^ 1 := by
  rw [pow_one]; exact h

private theorem maxContactIdeal_congr {k : Type u} [Field k] {X : Scheme.{u}}
    (p p' : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.LocallyOfFiniteType p']
    (hp : p = p') (I J : X.IdealSheafData) (hI : I = J) (m : ℕ) :
    maxContactIdeal k p I m = maxContactIdeal k p' J m := by
  subst hp
  subst hI
  rfl

namespace MarkedSequenceOfBlowups

def weakTransform {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E)
    (hN : ∀ j : ℕ, j ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length) (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i) :
    (u.schemeAt (i + 1)).IdealSheafData :=
  haveI : AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  controlledTransform (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le hb)

theorem exceptionalIdeal_mul_weakTransform {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E)
    (hN : ∀ j : ℕ, j ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length) (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i) :
    Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * u.weakTransform hN i hi b hb =
      b.comap (u.transitionMapSucc i) := by
  have : AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have h := exceptionalIdeal_pow_mul_controlledTransform (u.transitionMapSucc i) (u.center i) b 1
    (u.isBlowupAlongIdealSheaf_blowupMorphism i hi) (le_pow_one_of_le hb)
  rw [pow_one] at h
  exact h

theorem weakTransform_unique {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E)
    (hN : ∀ j : ℕ, j ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length) (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i)
    (c : (u.schemeAt (i + 1)).IdealSheafData)
    (hc : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c = b.comap (u.transitionMapSucc i)) :
    c = u.weakTransform hN i hi b hb := by
  have : AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have h : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) ^ 1 * c = b.comap (u.transitionMapSucc i) := by
    rw [pow_one]; exact hc
  exact eq_controlledTransform_of_mul_eq_comap (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le hb) c h

theorem weakTransform_le_maxContactIdeal {k : Type u} [Field k] [CharZero k]
    {V : Scheme.{u}} {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (hstep : MaxContactIdealComapLeControlled.{u})
    (u : MarkedSequenceOfBlowups q A μ E) (hμ : 1 ≤ μ)
    (hN : ∀ j : ℕ, j ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length)
    [AlgebraicGeometry.Smooth (u.projectionToBase i ≫ q)]
    [AlgebraicGeometry.LocallyOfFiniteType (u.projectionToBase i ≫ q)]
    [AlgebraicGeometry.Smooth (u.projectionToBase (i + 1) ≫ q)]
    [AlgebraicGeometry.LocallyOfFiniteType (u.projectionToBase (i + 1) ≫ q)]
    (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i)
    (hbm : b ≤ maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ) :
    u.weakTransform hN i hi b hb ≤
      maxContactIdeal k (u.projectionToBase (i + 1) ≫ q) (u.ideal (i + 1)) μ := by
  have : AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have hassoc : u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q) = u.projectionToBase (i + 1) ≫ q := by
    rw [← Category.assoc, ← SequenceOfBlowups.projectionToBase_succ]
  have : AlgebraicGeometry.Smooth (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) := by
    rw [hassoc]; infer_instance
  have : AlgebraicGeometry.LocallyOfFiniteType (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) := by
    rw [hassoc]; infer_instance
  have hAle : u.ideal i ≤ u.center i ^ μ :=
    le_pow_of_hasStrictNormalCrossingsWith (u.projectionToBase i ≫ q) (u.center i) (u.ideal i) (u.boundary i)
      (u.center_snc i hi) μ (u.center_order i hi)
  have hstep' := hstep k (u.schemeAt i) (u.schemeAt (i + 1)) (u.projectionToBase i ≫ q) (u.transitionMapSucc i)
    (u.center i) (u.boundary i) (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (u.ideal i) μ hμ hAle (u.ideal (i + 1)) (u.ideal_succ i hi)
  have hM : maxContactIdeal k (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) (u.ideal (i + 1)) μ =
      maxContactIdeal k (u.projectionToBase (i + 1) ≫ q) (u.ideal (i + 1)) μ :=
    maxContactIdeal_congr _ _ hassoc _ _ rfl μ
  rw [hM] at hstep'
  have h1 : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * u.weakTransform hN i hi b hb =
      b.comap (u.transitionMapSucc i) := exceptionalIdeal_mul_weakTransform u hN i hi b hb
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) :=
    ((isSmoothDivisor_iff (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) _).1
      (isSmoothDivisor_exceptionalIdeal (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi))).1
  refine hF.le_of_mul_le_mul ?_
  rw [h1]
  exact le_trans (Scheme.IdealSheafData.comap_mono (u.transitionMapSucc i) hbm) hstep'

end MarkedSequenceOfBlowups

private def strictTransformMaxContactIdeal {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E')
    (hN : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt i)) :
    ∀ i : ℕ, (u.schemeAt i).IdealSheafData := fun i =>
  Nat.rec (motive := fun j => (u.schemeAt j).IdealSheafData)
    ((maxContactIdeal k q A' μ).comap u.isoZero.hom)
    (fun j cj =>
      if h : j + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt (j + 1)) (hN (j + 1) h) (cj.comap (u.transitionMapSucc j))
          (Blowup.exceptionalIdeal (u.transitionMapSucc j) (u.center j))
      else ⊤) i

private theorem strictTransformMaxContactIdeal_succ {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E')
    (hN : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt i)) (i : ℕ) :
    strictTransformMaxContactIdeal u hN (i + 1) =
      if h : i + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt (i + 1)) (hN (i + 1) h)
          ((strictTransformMaxContactIdeal u hN i).comap (u.transitionMapSucc i))
          (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i))
      else ⊤ := rfl

private def maxContactIdealAt {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.Smooth q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E') (i : ℕ) (hi : i ≤ u.length) : (u.schemeAt i).IdealSheafData :=
  haveI := smooth_projectionToBase_comp u i hi
  maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ

theorem existsMaxContactControlledTransforms_of_comapLeControlled (h : MaxContactIdealComapLeControlled.{u}) :
    ExistsMaxContactControlledTransforms.{u} := by
  intro k _ _ V q _ _ A' μ hμ E' u hN hcen
  have sm : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.Smooth (u.projectionToBase i ≫ q) :=
    fun i hi => smooth_projectionToBase_comp u i hi
  have hcart : ∀ i : ℕ, i < u.length →
      Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) := by
    intro i hi
    have := sm i hi.le
    exact ((isSmoothDivisor_iff (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) _).1
      (isSmoothDivisor_exceptionalIdeal (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi))).1
  have hcen' : ∀ i : ℕ, (hi : i < u.length) →
      strictTransformMaxContactIdeal u hN i ≤ maxContactIdealAt u i hi.le → strictTransformMaxContactIdeal u hN i ≤ u.center i := by
    intro i hi hM
    have := sm i hi.le
    refine hcen i hi (strictTransformMaxContactIdeal u hN i) ?_
    have h1 : (((u.center i).support : Set ↥(u.schemeAt i))) ⊆ orderAtLeastLocus (u.ideal i) μ :=
      u.center_order i hi
    have h2 : (((maxContactIdealAt u i hi.le).support : Set ↥(u.schemeAt i))) = orderAtLeastLocus (u.ideal i) μ := by
      show (((maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ).support :
        Set ↥(u.schemeAt i))) = _
      rw [maxContactIdeal_eq_derivIdealSheafIterate]
      exact support_derivIdealSheafIterate_eq_orderAtLeastLocus k (u.projectionToBase i ≫ q) (u.ideal i) hμ
    have h3 : (((maxContactIdealAt u i hi.le).support : Set ↥(u.schemeAt i))) ⊆
        (((strictTransformMaxContactIdeal u hN i).support : Set ↥(u.schemeAt i))) := by
      exact_mod_cast Scheme.IdealSheafData.support_antitone hM
    rw [h2] at h3
    exact fun x hx => h3 (h1 hx)
  have heq' : ∀ i : ℕ, i < u.length → strictTransformMaxContactIdeal u hN i ≤ u.center i →
      Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * strictTransformMaxContactIdeal u hN (i + 1) =
        (strictTransformMaxContactIdeal u hN i).comap (u.transitionMapSucc i) := by
    intro i hi hb
    have hi' : i + 1 ≤ u.length := hi
    have : AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi'
    have hI : (strictTransformMaxContactIdeal u hN i).comap (u.transitionMapSucc i) ≤
        Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) ^ 1 :=
      comap_le_exceptionalIdeal_pow (u.transitionMapSucc i) (le_pow_one_of_le hb)
    rw [pow_one] at hI
    have hc : strictTransformMaxContactIdeal u hN (i + 1) =
        @idealSheafColon (u.schemeAt (i + 1)) (hN (i + 1) hi')
          ((strictTransformMaxContactIdeal u hN i).comap (u.transitionMapSucc i))
          (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) := by
      rw [strictTransformMaxContactIdeal_succ, dif_pos hi']
    rw [hc]
    exact (hcart i hi).mul_idealSheafColon hI
  have main : ∀ i : ℕ, (hi : i ≤ u.length) → strictTransformMaxContactIdeal u hN i ≤ maxContactIdealAt u i hi := by
    intro i
    induction i with
    | zero =>
      intro hi
      have := sm 0 hi
      have : AlgebraicGeometry.Smooth u.isoZero.hom := inferInstance
      have : AlgebraicGeometry.Smooth (u.isoZero.hom ≫ q) := inferInstance
      show strictTransformMaxContactIdeal u hN 0 ≤ maxContactIdeal k (u.projectionToBase 0 ≫ q) (u.ideal 0) μ
      have e1 : maxContactIdeal k (u.projectionToBase 0 ≫ q) (u.ideal 0) μ =
          maxContactIdeal k (u.isoZero.hom ≫ q) (A'.comap u.isoZero.hom) μ :=
        maxContactIdeal_congr _ _ (by rw [SequenceOfBlowups.projectionToBase_zero]) _ _ u.ideal_zero μ
      have e2 : maxContactIdeal k (u.isoZero.hom ≫ q) (A'.comap u.isoZero.hom) μ =
          (maxContactIdeal k q A' μ).comap u.isoZero.hom := by
        simp only [maxContactIdeal_eq_derivIdealSheafIterate]
        exact derivIdealSheafIterate_comap k q u.isoZero.hom (μ - 1) A'
      rw [e1, e2]
      exact le_rfl
    | succ j ih =>
      intro hj1
      have hj : j < u.length := hj1
      have ihj := ih hj.le
      have hb := hcen' j hj ihj
      have hw : strictTransformMaxContactIdeal u hN (j + 1) = u.weakTransform hN j hj (strictTransformMaxContactIdeal u hN j) hb :=
        MarkedSequenceOfBlowups.weakTransform_unique u hN j hj (strictTransformMaxContactIdeal u hN j) hb
          (strictTransformMaxContactIdeal u hN (j + 1)) (heq' j hj hb)
      have := sm j hj.le
      have := sm (j + 1) hj1
      rw [hw]
      exact MarkedSequenceOfBlowups.weakTransform_le_maxContactIdeal h u hμ hN j hj
        (strictTransformMaxContactIdeal u hN j) hb ihj
  exact ⟨strictTransformMaxContactIdeal u hN, rfl, fun i hi => heq' i hi (hcen' i hi (main i hi.le)),
    fun i hi => hcen' i hi (main i hi.le)⟩

end FunctorialResolution.EmbeddedResolution

end
