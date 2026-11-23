import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeAlgebraLiftMonoidSum
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeAlgebra_lift_monoid_sum : ∀ {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X), FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  first | exact @GlobalTheory.freeAlgebra_lift_eq_sum_monomials | exact GlobalTheory.freeAlgebra_lift_eq_sum_monomials | (intros; apply GlobalTheory.freeAlgebra_lift_eq_sum_monomials <;> assumption)
