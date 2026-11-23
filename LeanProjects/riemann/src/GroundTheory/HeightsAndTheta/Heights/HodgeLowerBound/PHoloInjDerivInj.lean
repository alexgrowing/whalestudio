import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicKernelFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem HoloInjDerivInj.proof : HoloInjDerivInj.Statement := by
  intro m f U hU hf hinj u hu
  have hdet : LinearMap.det (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) ≠ 0 :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
      IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof m U f hU hf.differentiableOn hinj u hu
  have hunit : IsUnit (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  exact ((Module.End.isUnit_iff _).1 hunit).injective

end GroundTheory.Heights₂.Heights.LowerBoundFree
