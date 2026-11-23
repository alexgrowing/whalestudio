import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
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
theorem _root_.GlobalTheory.T.majorantLength_twoSidedMoments_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A → ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧ ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤ ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  first | exact @GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | exact GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | (intros; apply GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap <;> assumption)
