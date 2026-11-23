import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem ConeProjHyperplaneNull.proof (hNull : NullSmaller.Statement)
    (hDim : ConeProjHyperplaneDim.Statement) : ConeProjHyperplaneNull.Statement := by
  intro n e P Ψ hP hΨ
  set J : Ideal (MvPolynomial (Fin n) ℂ) := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ

  have hlt : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (hDim n e P Ψ hP hΨ).trans_lt (by exact_mod_cast Nat.lt_succ_self e)

  refine measure_mono_null (fun z hz => ?_) (hNull n (e + 1) J hlt)
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [map_add, map_mul, hz.1 a ha, eval_coneFirstForm, hz.2, mul_zero, add_zero]

end GroundTheory.Heights₂.Heights
