import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDensity_continuousAt_zero_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧ ∀ τ, (mat x τ).det ≠ 0 := by
  first | exact @GlobalTheory.DensOne.dens_one | exact GlobalTheory.DensOne.dens_one | (intros; apply GlobalTheory.DensOne.dens_one <;> assumption)
