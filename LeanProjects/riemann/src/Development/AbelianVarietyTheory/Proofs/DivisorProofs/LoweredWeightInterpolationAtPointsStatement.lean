import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.loweredWeight_interpolation_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∀ j : Fin Fl.δ, ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ (∀ j', F (Fl.xs j') = if j' = j then 1 else 0) ∧ ∀ α : Fin (nd X.toData) → ℕ, ∑ q, α q ≤ Xa.T → (fun x => F x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)) ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s) := by
  first | exact @GlobalTheory.LowerInterp.lowered_interp | exact GlobalTheory.LowerInterp.lowered_interp | (intros; apply GlobalTheory.LowerInterp.lowered_interp <;> assumption)
