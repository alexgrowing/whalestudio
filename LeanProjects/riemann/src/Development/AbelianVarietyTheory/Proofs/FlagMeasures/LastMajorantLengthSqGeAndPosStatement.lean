import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_majorant_length_sq_ge_and_pos : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ g ∈ GG k r, Tz k r z ≤ lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < lenA k r z g a ∧ lenA k r z g a = lA k r z g a := by
  first | exact @GlobalTheory.LastLen.last_len | exact GlobalTheory.LastLen.last_len | (intros; apply GlobalTheory.LastLen.last_len <;> assumption)
