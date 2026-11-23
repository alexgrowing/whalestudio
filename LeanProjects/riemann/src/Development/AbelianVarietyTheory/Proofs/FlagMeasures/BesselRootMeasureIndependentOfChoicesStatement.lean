import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoices
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselRootMeasure_independent_of_choices : ∀ (D : Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : Mat D.R.k D.R.rS) (p p' : Point ℂ (D.R.rS + 1)) (μ μ' : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → γ ∈ GG D.R.k D.R.rS → Gf D.R.k D.R.rS z z' γ ≠ 0 → 0 < D.host.ka → Formalism.MainNotions.S.IsRootMeasR D z z' p γ μ → Formalism.MainNotions.S.IsRootMeasR D z z' p' γ μ' → p = p' ∧ μ = μ' ∧ IsHaarOn (Rset D.R.k D.R.rS γ) μ := by
  first | exact @GlobalTheory.SnMass.RootUniq.rootMeas_unique | exact GlobalTheory.SnMass.RootUniq.rootMeas_unique | (intros; apply GlobalTheory.SnMass.RootUniq.rootMeas_unique <;> assumption)
