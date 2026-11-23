import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_self_intersection_formula : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → Dominant O.Y (A.sh u s) → (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) → ∀ c, O.Y.arSelfC (O.Y.Mbar B u s) c = (T.K B c).top (T.L B c (A.sh u s) + (s : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phS (A.sh u s) s)) := by
  first | exact @GlobalTheory.ArSelfObj.arSelf_onObj | exact GlobalTheory.ArSelfObj.arSelf_onObj | (intros; apply GlobalTheory.ArSelfObj.arSelf_onObj <;> assumption)
