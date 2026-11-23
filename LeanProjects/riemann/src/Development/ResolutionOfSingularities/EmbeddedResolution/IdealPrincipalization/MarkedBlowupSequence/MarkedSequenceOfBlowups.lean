import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def withBotSuccToNat : WithBot ℕ∞ → ℕ
  | ⊥ => 0
  | (n : ℕ∞) => n.toNat + 1

theorem withBotSuccToNat_bot : withBotSuccToNat ⊥ = 0 := rfl

theorem withBotSuccToNat_coe (n : ℕ∞) : withBotSuccToNat (n : WithBot ℕ∞) = n.toNat + 1 := rfl

def krullDimSucc (X : Scheme.{u}) : ℕ := withBotSuccToNat (topologicalKrullDim ↥X)

theorem krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim (X : Scheme.{u}) : krullDimSucc X = withBotSuccToNat (topologicalKrullDim ↥X) := rfl

theorem krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le (X Y : Scheme.{u})
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by
  rcases eq_or_ne (topologicalKrullDim ↥X) ⊥ with hX | hX
  · simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, hX, withBotSuccToNat_bot]
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hX
    have hYne : topologicalKrullDim ↥Y ≠ ⊥ := by
      intro hb0
      rw [hb0, le_bot_iff] at h
      exact hX h
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hYne
    have hab : a ≤ b := by
      rw [← ha, ← hb] at h
      exact_mod_cast h
    have hbtop : b ≠ ⊤ := by
      intro hbt
      rw [← hb, hbt] at hY
      exact lt_irrefl _ hY
    have hatop : a ≠ ⊤ := by
      intro hat
      rw [hat, top_le_iff] at hab
      exact hbtop hab
    have hle : a.toNat ≤ b.toNat := by
      lift a to ℕ using hatop
      lift b to ℕ using hbtop
      simpa using hab
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim Y, ← ha, ← hb, withBotSuccToNat_coe, withBotSuccToNat_coe]
    omega

structure MarkedIdealWithBoundary : Type (u + 1) where
  base : Type u
  [instField : Field base]
  scheme : Scheme.{u}
  structMap : scheme ⟶ Spec (CommRingCat.of base)
  ideal : scheme.IdealSheafData
  mult : ℕ
  boundary : List scheme.IdealSheafData

attribute [instance] MarkedIdealWithBoundary.instField

theorem MarkedIdealWithBoundary.mk_eq_mk {k : Type u} [instk : Field k] (X : Scheme.{u}) (m : ℕ)
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData}
    {E E' : List X.IdealSheafData} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' := by
  subst hp
  subst hI
  subst hE
  rfl

abbrev MarkedIdealWithBoundary.krullDimSucc (T : MarkedIdealWithBoundary.{u}) : ℕ := EmbeddedResolution.krullDimSucc T.scheme

theorem MarkedIdealWithBoundary.krullDimSucc_eq_krullDimSucc_scheme (T : MarkedIdealWithBoundary.{u}) : T.krullDimSucc = EmbeddedResolution.krullDimSucc T.scheme := rfl

structure MarkedIdealWithBoundary.IsAdmissible (T : MarkedIdealWithBoundary.{u}) : Prop where
  charZero : CharZero T.base
  locallyOfFiniteType : AlgebraicGeometry.LocallyOfFiniteType T.structMap
  nonzeroOnComponents : NonzeroOnComponents T.ideal
  one_le_mult : 1 ≤ T.mult
  quasiCompact : AlgebraicGeometry.QuasiCompact T.structMap
  smooth : AlgebraicGeometry.Smooth T.structMap
  snc : InStrictNormalCrossingPosition T.structMap T.boundary

structure MarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toSequenceOfBlowups.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toSequenceOfBlowups.isoZero.hom)
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    AlgebraicGeometry.Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  center_order : ∀ i, i < toSequenceOfBlowups.length →
    ((toSequenceOfBlowups.center i).support : Set ↥(toSequenceOfBlowups.schemeAt i)) ⊆ orderAtLeastLocus (ideal i) m
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def projectionToSpec (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

theorem projectionToSpec_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.projectionToSpec i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

def exceptionalDivisor (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

theorem exceptionalDivisor_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.exceptionalDivisor i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

def lastIdeal (s : MarkedSequenceOfBlowups p I m E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq (s : MarkedSequenceOfBlowups p I m E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

def lastBoundary (s : MarkedSequenceOfBlowups p I m E) :
    List (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.boundary s.toSequenceOfBlowups.length

theorem lastBoundary_eq (s : MarkedSequenceOfBlowups p I m E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := rfl

def IsResolution (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  orderAtLeastLocus s.lastIdeal m = ∅

theorem isResolution_iff (s : MarkedSequenceOfBlowups p I m E) :
    s.IsResolution ↔ orderAtLeastLocus s.lastIdeal m = ∅ := Iff.rfl

end MarkedSequenceOfBlowups

def emptySequenceOfBlowups (X : Scheme.{u}) : SequenceOfBlowups X where
  length := 0
  tower := (CategoryTheory.Functor.const ℕᵒᵖ).obj X
  isoZero := Iso.refl X
  center := fun _ => ⊥
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)

theorem emptySequenceOfBlowups_length (X : Scheme.{u}) : (emptySequenceOfBlowups X).length = 0 := rfl

def emptyMarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := emptySequenceOfBlowups X
  ideal := fun _ => I.comap (emptySequenceOfBlowups X).isoZero.hom
  boundary := fun _ => E.map (fun D => D.comap (emptySequenceOfBlowups X).isoZero.hom)
  ideal_zero := rfl
  boundary_zero := rfl
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)

theorem emptyMarkedSequenceOfBlowups_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedSequenceOfBlowups p I m E).toSequenceOfBlowups.length = 0 := rfl

abbrev MarkedIdealWithBoundary.SequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) :=
  MarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

def PrincipalizationAssignment : Type (u + 1) := ∀ T : MarkedIdealWithBoundary.{u}, T.SequenceOfBlowups

theorem PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') :
    HEq (L T).toSequenceOfBlowups (L T').toSequenceOfBlowups := by
  subst h
  rfl

def trivialPrincipalizationAssignment : PrincipalizationAssignment.{u} :=
  fun (T : MarkedIdealWithBoundary.{u}) => emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

structure OrderReductionData : Type (u + 1) where
  maxOrderRed : PrincipalizationAssignment.{u}
  orderRed : PrincipalizationAssignment.{u}

def trivialOrderReductionData : OrderReductionData.{u} where
  maxOrderRed := trivialPrincipalizationAssignment
  orderRed := trivialPrincipalizationAssignment

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def HasReducedCenters (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  ∀ i, i < s.toSequenceOfBlowups.length → ∀ J : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData,
    ((s.toSequenceOfBlowups.center i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) ⊆
        (J.support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) →
      J ≤ s.toSequenceOfBlowups.center i

theorem markedSequenceOfBlowups_ideal_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.ideal 0 = I.comap (s.toSequenceOfBlowups.projectionToBase 0) := by
  rw [s.ideal_zero, s.toSequenceOfBlowups.projectionToBase_zero]

theorem markedSequenceOfBlowups_boundary_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.boundary 0 = E.map (fun D => D.comap (s.toSequenceOfBlowups.projectionToBase 0)) := by
  rw [s.boundary_zero, s.toSequenceOfBlowups.projectionToBase_zero]

theorem markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ (s : MarkedSequenceOfBlowups p I 1 E) (i : ℕ)
    (h : i < s.toSequenceOfBlowups.length) :
    Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) * s.ideal (i + 1) =
      (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
  have hs := s.ideal_succ i h
  rwa [pow_one] at hs

theorem markedSequenceOfBlowups_ideal_vanishesAlong_center (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    VanishesAlong (s.ideal i) (s.toSequenceOfBlowups.center i) := by
  rw [vanishesAlong_iff_le]
  refine hmax i h (s.ideal i) ?_
  intro x hx
  have hx' := s.center_order i h hx
  rw [mem_orderAtLeastLocus_one_iff] at hx'
  exact hx'

def MarkedSequenceOfBlowups.toIdealBlowupSequence (s : MarkedSequenceOfBlowups p I 1 E) (hmax : HasReducedCenters s) :
    IdealBlowupSequence p I E where
  toSequenceOfBlowups := s.toSequenceOfBlowups
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := markedSequenceOfBlowups_ideal_zero s
  boundary_zero := markedSequenceOfBlowups_boundary_zero s
  center_smooth := s.center_smooth
  center_snc := s.center_snc
  ideal_vanishes := fun i h => markedSequenceOfBlowups_ideal_vanishesAlong_center s hmax i h
  ideal_succ := fun i h => markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ s i h
  boundary_succ := s.boundary_succ

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).toSequenceOfBlowups = s.toSequenceOfBlowups := rfl

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).lastIdeal = s.lastIdeal := rfl

end

end FunctorialResolution.EmbeddedResolution
