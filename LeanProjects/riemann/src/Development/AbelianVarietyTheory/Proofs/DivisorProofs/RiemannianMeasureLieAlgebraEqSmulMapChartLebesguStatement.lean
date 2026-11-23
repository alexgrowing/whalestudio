import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesgu
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), 1 ≤ r → IsOrth X x → ∀ D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ), (∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧ ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ)) → Function.Injective D ∧ riemLie X.Ψ X.Gm x = ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) • (volume : Measure (ChartSp X)).map D := by
  first | exact @GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | exact GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | (intros; apply GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map <;> assumption)
