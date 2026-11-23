import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.momentPieriNumerics_of_sizeHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (U : ℕ → ℝ), (∀ i : Fin D.R.k, U (i.val + 1) = uS D w τ i) → Num D.R.k D.R.rS (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) ∧ GapCell D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) ∧ PI.BesselPeriodGGP.eps48 D.R.k D.R.rS = epsSH D.R := by
  first | exact @GlobalTheory.SizeNum.num_of_size | exact GlobalTheory.SizeNum.num_of_size | (intros; apply GlobalTheory.SizeNum.num_of_size <;> assumption)
