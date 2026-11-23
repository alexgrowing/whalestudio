import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
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
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem toMarkedSequence_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = s.proj i :=
  (s.projectionToBase_eq_toSequenceOfBlowups i).symm

theorem isPullbackBlowupSequence_congr (F : PrincipalizationAssignment.{u})
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] {B Q : Scheme.{u}}
    (pB : B ⟶ Spec (CommRingCat.of k₁)) (IB : B.IdealSheafData) (mB : ℕ)
    (EB : List B.IdealSheafData) (q : Q ⟶ B)
    (pQ₁ pQ₂ : Q ⟶ Spec (CommRingCat.of k₂)) (IQ₁ IQ₂ : Q.IdealSheafData) (mQ₁ mQ₂ : ℕ)
    (EQ₁ EQ₂ : List Q.IdealSheafData)
    (hp : pQ₁ = pQ₂) (hI : IQ₁ = IQ₂) (hm : mQ₁ = mQ₂) (hE : EQ₁ = EQ₂)
    (h : IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₁ IQ₁ mQ₁ EQ₁)).toSequenceOfBlowups
        (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₂ IQ₂ mQ₂ EQ₂)).toSequenceOfBlowups
      (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

theorem BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length = s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  rfl

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt {X : Scheme.{u}} (s : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt j = s.schemeAt j :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt _ j).trans (BlowupSequenceData.ofSequenceOfBlowups_schemeAt s j)

private theorem le_length_of_le_ofSequenceOfBlowups_length {X : Scheme.{u}} (s : SequenceOfBlowups X) {j : ℕ}
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length) : j ≤ s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact hj

private theorem le_ofSequenceOfBlowups_length_of_le_length {X : Scheme.{u}} (s : SequenceOfBlowups X) {j : ℕ}
    (hj : j ≤ s.length) : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

theorem BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups {X : Scheme.{u}} (t : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.projectionToBase j = t.projectionToBase j :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups t) j).trans (BlowupSequenceData.ofSequenceOfBlowups_projectionToBase t j)

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

private def ofSequenceOfBlowupsMap (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j)).symm

private theorem index_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    c.idx (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s]
  exact c.idx_length

private theorem index_lt_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      c.idx j < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact c.idx_lt j hj

private theorem index_lt_index_succ_of_lt_length_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact c.idx_strictMono j hj

private theorem ofSequenceOfBlowups_map_eq (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    ofSequenceOfBlowupsMap c j hj = c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) := by
  show 𝟙 (s'.schemeAt j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) ≫ 𝟙 (s.schemeAt (c.idx j))
      = c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj)
  exact (Category.id_comp _).trans (Category.comp_id _)

private theorem isPullback_congr {A B C D : Scheme.{u}} {f f' : A ⟶ B} {g g' : A ⟶ C}
    {h h' : B ⟶ D} {k k' : C ⟶ D} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f g h k) : IsPullback f' g' h' k' := by
  subst hf
  subst hg
  subst hh
  subst hk
  exact H

private theorem isPullback_projectionToBase_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      IsPullback (ofSequenceOfBlowupsMap c j hj) ((BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.projectionToBase j)
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr (ofSequenceOfBlowups_map_eq c j hj).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)).symm rfl
    (c.isPullback j (le_length_of_le_ofSequenceOfBlowups_length s' hj))

private theorem ofSequenceOfBlowups_transitionMap {W : Scheme.{u}} (t : SequenceOfBlowups W) {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap h = t.transitionMap h := by
  induction h with
  | refl =>
      have e1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (le_refl i) = 𝟙 ((BlowupSequenceData.ofSequenceOfBlowups t).obj i) := by
        rw [BlowupSequenceData.transitionMap_refl]
      have e2 : t.transitionMap (le_refl i) = 𝟙 (t.schemeAt i) := by
        rw [SequenceOfBlowups.transitionMap_self_eq_id]
      exact e1.trans e2.symm
  | @step m hm ih =>
      have hmap : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) = t.transitionMapSucc m :=
        (BlowupSequenceData.transitionMap_succ (BlowupSequenceData.ofSequenceOfBlowups t) m).trans (BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism t m)
      have h1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_trans hm (Nat.le_succ m))
          = (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        (BlowupSequenceData.transitionMap_comp_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) hm (Nat.le_succ m)).symm
      have h2a : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        congrArg (fun f : t.schemeAt (m + 1) ⟶ t.schemeAt m => f ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm) hmap
      have h2b : t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ t.transitionMap hm :=
        congrArg (fun g : t.schemeAt m ⟶ t.schemeAt i => t.transitionMapSucc m ≫ g) ih
      have h3 : t.transitionMapSucc m ≫ t.transitionMap hm = t.transitionMap (Nat.le_trans hm (Nat.le_succ m)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact SequenceOfBlowups.transitionMap_trans t hm (Nat.le_succ m)
      exact h1.trans (h2a.trans (h2b.trans h3))

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap {W : Scheme.{u}} (t : SequenceOfBlowups W) {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap h = t.transitionMap h :=
  (BlowupSequenceData.toSequenceOfBlowups_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) h).trans (ofSequenceOfBlowups_transitionMap t h)

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism {W : Scheme.{u}} (t : SequenceOfBlowups W) (i : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMapSucc i = t.transitionMapSucc i :=
  (SequenceOfBlowups.blowupMorphism_eq_transitionMap ((BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups) i).trans
    ((ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap t (Nat.le_succ i)).trans
      (SequenceOfBlowups.blowupMorphism_eq_transitionMap t i).symm)

private theorem ofSequenceOfBlowups_blowupMorphism_comp_map (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.transitionMapSucc j ≫ ofSequenceOfBlowupsMap c j (le_of_lt hj) =
        ofSequenceOfBlowupsMap c (j + 1) hj ≫
          (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c j hj)) := by
  intro j hj
  have hlt : j < s'.length := by
    have h := hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
    exact h
  rw [ofSequenceOfBlowups_map_eq c j (le_of_lt hj), ofSequenceOfBlowups_map_eq c (j + 1) hj,
    ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap]
  exact c.step j hlt

private theorem eqToHom_refl_comp_comp_eqToHom_refl {A B : Scheme.{u}} (hA : A = A) (hB : B = B)
    (f : A ⟶ B) : eqToHom hA ≫ f ≫ eqToHom hB = f := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem center_ofSequenceOfBlowups_eq_comap (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j =
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center (c.idx j)).comap (ofSequenceOfBlowupsMap c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  have hmap : ofSequenceOfBlowupsMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j)).symm
      (c.map j (le_length_of_le_ofSequenceOfBlowups_length s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

private theorem center_ofSequenceOfBlowups_ne_top (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  exact c.center_ne_top j hj'

private theorem ofSequenceOfBlowups_ne_of_mem_unmatched_center (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ i : ℕ, i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length →
      (∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt i),
        z ∈ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < s.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hi
    exact hi
  have hmiss' : ∀ j : ℕ, j < s'.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i]
  exact h

def toBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ s' s) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups where
  idx := c.idx
  map := ofSequenceOfBlowupsMap c
  idx_length := index_ofSequenceOfBlowups_length c
  idx_lt := index_lt_ofSequenceOfBlowups_length c
  idx_strictMono := index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c
  isPullback := isPullback_projectionToBase_ofSequenceOfBlowups c
  step := ofSequenceOfBlowups_blowupMorphism_comp_map c
  center_comap := center_ofSequenceOfBlowups_eq_comap c
  center_ne_top := center_ofSequenceOfBlowups_ne_top c
  omitted := ofSequenceOfBlowups_ne_of_mem_unmatched_center c

private def transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm ≫ c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))

private theorem ofSequenceOfBlowups_index_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    c.idx s'.length = s.length := by
  have h := c.idx_length
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s] at h
  exact h

private theorem ofSequenceOfBlowups_index_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < s.length := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.idx_lt j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
  exact h

private theorem index_lt_index_succ_of_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

private theorem transportedMap_eq_map
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) :
    transportedMap c j hj = c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) :=
  eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))
    (c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj))

private theorem isPullback_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j ≤ s'.length),
      IsPullback (transportedMap c j hj) (s'.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr (transportedMap_eq_map c j hj).symm (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j)
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)) rfl
    (c.isPullback j (le_ofSequenceOfBlowups_length_of_le_length s' hj))

private theorem blowupMorphism_comp_map_of_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.transitionMapSucc j ≫ transportedMap c j (le_of_lt hj) =
        transportedMap c (j + 1) hj ≫ s.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length c j hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have key := c.step j hj'
  rw [ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap] at key
  rw [transportedMap_eq_map c j (le_of_lt hj), transportedMap_eq_map c (j + 1) hj]
  exact key

private theorem center_eq_comap_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.center j = (s.center (c.idx j)).comap (transportedMap c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have hmap : transportedMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))
      (c.map j (le_ofSequenceOfBlowups_length_of_le_length s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

private theorem center_ne_top_of_pullback_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  exact c.center_ne_top j hj'

private theorem ofSequenceOfBlowups_projectionToBase_ne
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hi
  have hmiss' : ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i] at h
  exact h

def ofBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ s' s where
  idx := c.idx
  map := transportedMap c
  idx_length := ofSequenceOfBlowups_index_length c
  idx_lt := ofSequenceOfBlowups_index_lt_length c
  idx_strictMono := index_lt_index_succ_of_lt_length c
  isPullback := isPullback_transportedMap c
  step := blowupMorphism_comp_map_of_ofSequenceOfBlowups c
  center_comap := center_eq_comap_transportedMap c
  center_ne_top := center_ne_top_of_pullback_ofSequenceOfBlowups c
  omitted := ofSequenceOfBlowups_projectionToBase_ne c

end SequenceOfBlowupsPullback

end FunctorialResolution.EmbeddedResolution

end
