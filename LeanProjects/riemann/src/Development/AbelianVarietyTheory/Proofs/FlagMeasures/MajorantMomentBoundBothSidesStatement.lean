import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSides
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantMomentBound_both_sides : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S → MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧ MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  first | exact @GlobalTheory.Amp.MomBoth.momBd_both | exact GlobalTheory.Amp.MomBoth.momBd_both | (intros; apply GlobalTheory.Amp.MomBoth.momBd_both <;> assumption)
