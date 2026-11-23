import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup : ∀ (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (E i)) → ∀ g : Formalism.REAL.UJ ε, (uMat g - 1) - Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε ∈ Submodule.span ℝ (Set.range E) → ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ Formalism.REAL.hs (uMat g - 1) ∧ Formalism.REAL.hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + Formalism.REAL.hs (uMat g - 1) ^ 2 / 4 := by
  first | exact @GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | exact GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | (intros; apply GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le <;> assumption)
