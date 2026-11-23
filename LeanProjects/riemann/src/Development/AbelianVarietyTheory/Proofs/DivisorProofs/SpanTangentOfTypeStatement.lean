import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTangentOfType
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_tangent_of_type_of_isBasis : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p d h : ℕ) (ty : Fin d → ZMod h)
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), IsBasis G p ty γ →
    ∀ (t : ZMod h) (w : Fin d → C), (∀ c, ty c ≠ t → w c = 0) →
      w ∈ Submodule.span C (Set.range fun b : {b // ty b = t} => tangent (γ b.1)) := by
  first | exact @GlobalTheory.span_tangent_of_type | exact GlobalTheory.span_tangent_of_type | (intros; apply GlobalTheory.span_tangent_of_type <;> assumption)
