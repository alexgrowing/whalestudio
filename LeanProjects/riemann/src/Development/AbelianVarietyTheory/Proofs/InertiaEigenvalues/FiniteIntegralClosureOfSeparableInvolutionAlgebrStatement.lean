import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIntegralClosureOfSeparableInvolutionAlgebr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  first | exact @GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | exact GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | (intros; apply GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure <;> assumption)
