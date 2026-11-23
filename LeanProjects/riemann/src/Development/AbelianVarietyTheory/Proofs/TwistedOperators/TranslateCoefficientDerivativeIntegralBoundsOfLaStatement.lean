import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws : EmbLaws → PowInt → DecPow → LieBound → DerBounds := by
  first | exact @GlobalTheory.SepReal.DerInt.derBounds_of | exact GlobalTheory.SepReal.DerInt.derBounds_of | (intros; apply GlobalTheory.SepReal.DerInt.derBounds_of <;> assumption)
