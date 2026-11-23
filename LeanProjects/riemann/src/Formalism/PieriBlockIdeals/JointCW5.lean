import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.StatementC

noncomputable section

namespace Formalism.CohomologicalDescent

open Formalism.RankGapBounds.ChebyshevFactorialBounds

def JointCW5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (τ : ι) (l : ℕ), l.Prime → τ ∈ D.T2 → D.Params → D.h < l ^ 2 →
    ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)) + (D.ecl τ l : ℝ) +
        labelLHS l D.k D.t (D.depth τ l : ℝ) (D.xlo τ) (D.xhi τ) (D.maxB τ) ≤
      Cor.coefficientBoundTau D τ l

end Formalism.CohomologicalDescent
