import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem mem_support_cycleSection_iff {n : ℕ} (Z : ProjCycle ℂ n) (u : Fin n → ℂ)
    (W' : Ideal (MvPolynomial (Fin n) ℂ)) :
    W' ∈ (cycleSection Z u).support ↔ ∃ W ∈ Z.support, W' ∈ (divCycle W u).support := by
  simp only [Finsupp.mem_support_iff, cycleSection, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, not_forall, mul_eq_zero, not_or, exists_prop]
  constructor <;> rintro ⟨W, h⟩ <;> exact ⟨W, by tauto⟩

theorem SupportCycleSection.proof : SupportCycleSection.Statement := by
  intro n Z u
  refine ⟨fun W hW W' hW' => (mem_support_cycleSection_iff Z u W').mpr ⟨W, hW, hW'⟩,
    fun W' hW' => (mem_support_cycleSection_iff Z u W').mp hW'⟩

end GroundTheory.Heights₂.Heights
