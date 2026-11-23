import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselDoubleCosetMeasureBigCellEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μG μW μW' : Measure (Mt k r)) (c κ : ℝ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec → 0 < c → 0 < κ → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → IsHaarOn (UWset k r z') μW' → μW' Set.univ = 1 → AEMeasurable (fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) (volume.withDensity fun q => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)) ∧ IsDis (Greg k r z z') μG (muProd μW (haarLie (Nset k r) (ENNReal.ofReal κ))) (muProd μW' (haarLie (Nset k r) (ENNReal.ofReal κ))) (ENNReal.ofReal (c * 2 ^ (r + 1) * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k / κ ^ 2) • (volume.withDensity fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)).map fun q => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) := by
  first | exact @GlobalTheory.DoubleCosetMeasure.isDis_bigCell | exact GlobalTheory.DoubleCosetMeasure.isDis_bigCell | (intros; apply GlobalTheory.DoubleCosetMeasure.isDis_bigCell <;> assumption)
