import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in

theorem integralClosure_projective_rA : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F),
    IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  intro k _ _ F K _ _ _ _ _ _ d x h i
  obtain ⟨hfin, -, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x h {i} (Finset.singleton_nonempty i)
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h.pd i
  haveI : IsRegularRing (rA k x {i}) := IsRegularRing.of_ringEquiv e.toRingEquiv
  haveI : IsNoetherianRing (rA k x {i}) := inferInstance
  haveI : IsDomain (rA k x {i}) := inferInstance
  haveI : IsIntegrallyClosed (rA k x {i}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {i}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI : IsRegularRing (rB k K x {i}) := GlobalTheory.isRegularRing_of_smooth k _
  haveI hB : IsRegularRing (integralClosure (rA k x {i}) K) := ‹IsRegularRing (rB k K x {i})›
  haveI : IsNoetherianRing (integralClosure (rA k x {i}) K) := inferInstance
  haveI : IsDomain (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Algebra.IsIntegral (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : FaithfulSMul (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun y : integralClosure (rA k x {i}) K => (y : K)) hab
    exact Subtype.ext ((algebraMap F K).injective this)
  haveI : Algebra.HasGoingDown (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Module.Flat (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    refine GlobalTheory.flat_of_isRegularRing_of_isRegularRing fun q hq => ?_
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under (rA k x {i})) q]
    · exact le_self_add
    all_goals first | assumption | infer_instance
  haveI : Module.FinitePresentation (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory
