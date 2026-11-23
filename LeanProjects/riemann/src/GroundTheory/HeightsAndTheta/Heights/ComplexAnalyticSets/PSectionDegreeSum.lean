import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionDegreeSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SectionDegreeSum.proof (h : ChowFormSection.Statement) : SectionDegreeSum.Statement := by
  intro F _ _ n e δ I f u hI hf hδ hu
  obtain ⟨c, hc, g, hg, heq⟩ := h F n (e + 1) I f u hI hf hu
  have hδs : IsMultiHomog δ (specFirst f u) := hδ.specFirst u
  rw [heq] at hδs
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hδs hne
  exact ⟨g, δW, fun W hW => ⟨isProjPrime_of_mem_support_divCycle hI u hW, hg W hW, hδW W hW⟩,
    hsum.symm⟩

end GroundTheory.Heights₂.Heights
