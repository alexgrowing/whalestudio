import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasisReTraceMulConjTranspose
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' : ∀ (n : ℕ) (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧ U = Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | exact GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | (intros; apply GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose <;> assumption)
