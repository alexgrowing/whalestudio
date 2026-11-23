import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε R : ℝ), x ∈ X.dom → 0 < ε → 0 ≤ R → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ R}.encard : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt (R / ε)) ^ (2 * fdeg E * r)) := by
  first | exact @GlobalTheory.LatCount.encard_le | exact GlobalTheory.LatCount.encard_le | (intros; apply GlobalTheory.LatCount.encard_le <;> assumption)
