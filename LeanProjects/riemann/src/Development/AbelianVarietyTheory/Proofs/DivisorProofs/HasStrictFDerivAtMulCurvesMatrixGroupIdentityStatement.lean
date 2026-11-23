import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentity
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  first | exact @GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | exact GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | (intros; apply GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity <;> assumption)
