import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isOrderReduction_maxContact_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (hlow : IsMaxOrderReduction Q L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L) :
    IsOrderReduction P (maxContactPrincipalization hinv A) L := by
  refine
    { cert := ?_, base_change := ?_, base_change_strict := ?_, pushforward := ?_,
      order_le := ?_, center_nonempty := ?_, resolves := ?_, smooth_pullback := ?_,
      smooth_pullback_strict := ?_, trivial_of_coSupport_empty := ?_ }
  · intro T hv hdim hO i hi
    exact orderCertificate_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE hV'
      hP' hord
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE
      hV' hP' hord
  · intro T hv hdim hO hbdry hmult Y q e _ hq hsm J hJv hJd hJi
    exact isPushforward_of_isSmoothDivisor hinv P Q A L L' hstar hdes hdiv hlow hdimlink T hv hdim hO
      hbdry hmult Y q e hq hsm J hJv hJd hJi
  · intro T hv hdim hO i hi x
    exact orderAt_ideal_le_mult hinv P A L hdes T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi x
  · intro T hv hdim hO i hi
    exact center_support_nonempty hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO
    exact isResolution_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO)
  · intro T hv hdim hO Y q g _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq E' hBE
      hV' hP' hord
  · intro T hv hdim hO Y q g _ _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq
      E' hBE hV' hP' hord
  · intro T hv hdim hO hemp
    exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) hemp

theorem isOrderReduction_maxContact_dim_le_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hstar : CoverSequenceProperties hinv (fun d => d ≤ n) A)
    (hdes : DescentHypotheses hinv (fun d => d ≤ n) A L) :
    IsOrderReduction (fun d => d ≤ n) (maxContactPrincipalization hinv A) L :=
  isOrderReduction_maxContact_of_descentHypotheses hinv (fun d => d ≤ n) (fun d => d < n) A L L'
    (fun _ _ hab hb => lt_of_lt_of_le hab hb) hlow hdiv hstar hdes

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
