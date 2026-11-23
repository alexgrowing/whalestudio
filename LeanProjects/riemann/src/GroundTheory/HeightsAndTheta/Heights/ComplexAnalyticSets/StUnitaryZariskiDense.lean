import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def UnitaryZariskiDense.Statement : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ), p ≠ 0 →
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun ij : Fin n × Fin n => U ij.1 ij.2) p ≠ 0

end

end GroundTheory.Heights₂.Heights.ComplexSets
