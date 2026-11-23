import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPlurisubharmonicCorrection
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_plurisubharmonic_correction : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c σ, ∃ (b : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)) (p : (T.M c).X σ → ℝ), IsPoin ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) b p ∧ ∃ C : ℝ, ∀ C' : ℝ, C ≤ C' → ∀ u (R : ℝ), 2 ≤ R → DomL O.Y.j u → PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + ReciprocityTheory.AnForm.M.LocPot.ofFun ((T.F c).phR R u σ) + (b + ReciprocityTheory.AnForm.M.LocPot.ofFun p).rsmul (C' * ‖u‖)) := by
  first | exact @GlobalTheory.CurvInterp.curv_interp_lower | exact GlobalTheory.CurvInterp.curv_interp_lower | (intros; apply GlobalTheory.CurvInterp.curv_interp_lower <;> assumption)
