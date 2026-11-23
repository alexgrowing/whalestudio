import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_bigCell_haar_density_constant : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  first | exact @GlobalTheory.CellDens.bigCell_integral | exact GlobalTheory.CellDens.bigCell_integral | (intros; apply GlobalTheory.CellDens.bigCell_integral <;> assumption)
