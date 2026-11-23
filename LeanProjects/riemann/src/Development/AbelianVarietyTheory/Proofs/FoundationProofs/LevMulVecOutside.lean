import Mathlib
import Formalism.FormalDegreeBessel.StatementRP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramRight

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.LevelStabiliser

open GlobalTheory.LevelUnitary

variable (k i r' : ℕ)

theorem liftVec_eq (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k i r' v = incl k i r' *ᵥ v := by
  ext p
  have h := incl_mul k i r' (Matrix.of fun a (_ : Unit) => v a) p ()
  exact h.symm

end GlobalTheory.LevelStabiliser
