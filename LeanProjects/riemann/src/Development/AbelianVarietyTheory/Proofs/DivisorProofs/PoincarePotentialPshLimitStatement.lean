import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincarePotentialPshLimit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_potential_psh_limit : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ (c : O.Y.Comp) (u : Wt O.Y), (∀ τ, StrictAnti (u τ)) → ∀ σ : Fin ((T.M c).n + 1), ∃ (b : LocPot ((T.M c).X σ)) (p : (T.M c).X σ → ℝ), IsPoin ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) b p ∧ ∃ t : ℝ, ∀ᶠ R in atTop, PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + LocPot.ofFun (psiOf h x' R u c σ) + (b + LocPot.ofFun p).rsmul t) := by
  first | exact @GlobalTheory.ArDegIndep.CurvOther.curv_other | exact GlobalTheory.ArDegIndep.CurvOther.curv_other | (intros; apply GlobalTheory.ArDegIndep.CurvOther.curv_other <;> assumption)
