import Formalism.PieriBlockIdeals.StatementJ
import Formalism.RankGapBounds.RankGapProofs.CardLargePrimeFactorsLeOneHolds
import Mathlib
import Formalism.PieriBlockIdeals.PieriColumnMinors.MaxValEqZeroOfLt
import Formalism.PieriBlockIdeals.PieriColumnMinors.LocalComponentGL

open Finset

namespace Formalism.CohomologicalDescent.Joint

open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.Cor

theorem cloud_anti {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : StrictAnti (W.cloud τ) := by
  intro a b hab
  refine W.anti τ ?_
  have : (a : ℕ) < (b : ℕ) := hab
  exact this

theorem rest_anti {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : StrictAnti (W.rest τ) := by
  intro a b hab
  refine W.anti τ ?_
  have : (a : ℕ) < (b : ℕ) := hab
  simp only [Fin.lt_def]
  omega

end Formalism.CohomologicalDescent.Joint
