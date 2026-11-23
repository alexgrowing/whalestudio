import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreementOfPolynomialFamilies
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.agreement_of_polynomial_families : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y), (∀ c, (T.F c).FamR Y.j) → (∀ c, (T.F c).FamS) → TiePs T A → TieM T A → Agree A := by
  first | exact @GlobalTheory.Mean4O.agree_of_families | exact GlobalTheory.Mean4O.agree_of_families | (intros; apply GlobalTheory.Mean4O.agree_of_families <;> assumption)
