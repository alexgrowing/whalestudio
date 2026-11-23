import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankOneUnitaryIntegrationFormulaExactConstant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_unitary_integration_formula_exact_constant : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μb μW μW' : Measure (Mt k r)) (cb : ℝ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec → 0 < cb → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → IsHaarOn (UWset k r z') μW' → μW' Set.univ = 1 → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = ENNReal.ofReal (cb * 2 * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k) * ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * Formalism.FourierDecayAlt.B2.embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW') := by
  first | exact @GlobalTheory.RankOneExact.rankOne_exact | exact GlobalTheory.RankOneExact.rankOne_exact | (intros; apply GlobalTheory.RankOneExact.rankOne_exact <;> assumption)
