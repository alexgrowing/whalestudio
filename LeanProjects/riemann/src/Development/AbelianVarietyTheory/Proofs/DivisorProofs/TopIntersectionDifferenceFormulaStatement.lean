import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIntersectionDifferenceFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_intersection_difference_formula : ∀ (e : ℕ) (M : Man e) (K : Calc M) (v : K.V) (u : M.Fun), M.Smooth u → K.top (v + K.ar u) - K.top v = ∑ i ∈ Finset.range (e + 1), M.int (fun l : Fin e => if (l : ℕ) < i then K.c1 (v + K.ar u) else K.c1 v) u := by
  first | exact @GlobalTheory.Mean4O.top_add_ar_sub | exact GlobalTheory.Mean4O.top_add_ar_sub | (intros; apply GlobalTheory.Mean4O.top_add_ar_sub <;> assumption)
