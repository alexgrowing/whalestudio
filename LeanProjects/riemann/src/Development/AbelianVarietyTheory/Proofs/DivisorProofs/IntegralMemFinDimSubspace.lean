import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualMemSpanEvalOfFiniteDimensional
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ

end GlobalTheory
