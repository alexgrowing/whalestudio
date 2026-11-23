import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  first | exact @GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | exact GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | (intros; apply GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero <;> assumption)
