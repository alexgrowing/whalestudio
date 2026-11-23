import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def MaxContactHypersurfacesEtaleEquivalent : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u})
      (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ →
    IsMaxContactInvariant k p A μ →
    (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
    ∀ (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData),
      InStrictNormalCrossingPosition p (H₁ :: N) → InStrictNormalCrossingPosition p (H₂ :: N) →
      IsMaxContactHypersurface k p A μ H₁ → IsMaxContactHypersurface k p A μ H₂ →
      ∃ (V : Scheme.{u}) (ψ₁ ψ₂ : V ⟶ P) (_ : AlgebraicGeometry.Etale ψ₁)
        (_ : AlgebraicGeometry.Etale ψ₂)
        (_ : AlgebraicGeometry.QuasiCompact (ψ₁ ≫ p))
        (hft : AlgebraicGeometry.LocallyOfFiniteType (ψ₁ ≫ p)),
        ψ₁ ≫ p = ψ₂ ≫ p ∧
        orderAtLeastLocus A μ ⊆ Set.range ψ₁.base ∧
        orderAtLeastLocus A μ ⊆ Set.range ψ₂.base ∧
        A.comap ψ₁ = A.comap ψ₂ ∧
        H₁.comap ψ₁ = H₂.comap ψ₂ ∧
        N.map (fun D => D.comap ψ₁) = N.map (fun D => D.comap ψ₂) ∧
        (@maxContactIdeal k _ _ V (ψ₁ ≫ p) hft (A.comap ψ₁) μ).subschemeι ≫ ψ₁ =
          (@maxContactIdeal k _ _ V (ψ₁ ≫ p) hft (A.comap ψ₁) μ).subschemeι ≫ ψ₂

def ExistsMaxContactControlledTransforms : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (V : Scheme.{u})
      (q : V ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
      [AlgebraicGeometry.LocallyOfFiniteType q]
      (A' : V.IdealSheafData) (μ : ℕ), 1 ≤ μ →
    ∀ (E' : List V.IdealSheafData) (u : MarkedSequenceOfBlowups q A' μ E'),
      (∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsLocallyNoetherian (u.schemeAt i)) →
      (∀ i : ℕ, i < u.length → ∀ J : (u.schemeAt i).IdealSheafData,
        (((u.center i).support : Set ↥(u.schemeAt i)) ⊆ ((J.support : Set ↥(u.schemeAt i)))) →
        J ≤ u.center i) →
      ∃ c : ∀ i : ℕ, (u.schemeAt i).IdealSheafData,
        c 0 = (maxContactIdeal k q A' μ).comap u.isoZero.hom ∧
        (∀ i : ℕ, i < u.length →
          Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c (i + 1) =
            (c i).comap (u.transitionMapSucc i)) ∧
        (∀ i : ℕ, i < u.length → c i ≤ u.center i)

namespace OrderReduction

structure OrderReductionHypotheses : Prop where
  maxContactChain : ExistsMaxContactControlledTransforms.{u}
  center_mem_coSupport : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult
  dBalanced_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
        [AlgebraicGeometry.LocallyOfFiniteType q],
      IsDerivBalanced T.base T.structMap T.ideal T.mult →
      IsDerivBalanced T.base q (T.ideal.comap h) T.mult
  schemeDim_le_of_etale : ∀ (V P : Scheme.{u}) (f : V ⟶ P) [AlgebraicGeometry.Etale f]
      [AlgebraicGeometry.IsLocallyNoetherian P],
      topologicalKrullDim ↥P < ⊤ → krullDimSucc V ≤ krullDimSucc P
  isLocallyNoetherian_obj : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i)
  lifting : BlowupLiftEqOnControlledTransform.{u}
  smooth_center_radical : ∀ (k : Type u) [Field k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
      ∀ J : X.IdealSheafData,
        (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z
  etaleEqualization : MaxContactHypersurfacesEtaleEquivalent.{u}
  isStrictPullbackSeq : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
      (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
      (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
      (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
        (s.projectionToBase i).base x ∈ Set.range φ.base) →
      IsStrictPullbackBlowupSeq φ s' s
  valid_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

end OrderReduction

end FunctorialResolution.EmbeddedResolution

end
