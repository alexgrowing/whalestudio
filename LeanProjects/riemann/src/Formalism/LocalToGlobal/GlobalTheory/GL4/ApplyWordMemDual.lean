import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def liftWord {n : ℕ} (w : List (Fin n × Fin n × ℕ)) : List (Fin (n + 1) × Fin (n + 1) × ℕ) :=
  w.map fun x => (x.1.castSucc, x.2.1.castSucc, x.2.2)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
