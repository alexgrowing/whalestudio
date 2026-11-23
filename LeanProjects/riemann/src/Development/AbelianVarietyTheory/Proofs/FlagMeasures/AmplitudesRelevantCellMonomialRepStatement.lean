import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudes_relevant_cell_monomial_rep : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W) (hA : GoodS D lam0 A₀) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'), 0 < θ → 0 < D.host.ka / gg D → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR → ∃ (g₀ : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ), CellData (toBessel D τ w w' θ W lam0 A₀ hW hA hT hT') W.μG g₀ μR ν₀ ν ∧ ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧ (∀ l, DminN W.z W.z' γ l = DminN W.z W.z' g₀ l) ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → A.J νR γ = s • A.J ν₀ g₀ := by
  first | exact @GlobalTheory.CellRed.amp_at_monomial | exact GlobalTheory.CellRed.amp_at_monomial | (intros; apply GlobalTheory.CellRed.amp_at_monomial <;> assumption)
