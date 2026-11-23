import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem DefectSymm.proof (h1 : CycleSectionData.Statement) (h2 : SpecFirstSwapMahler.Statement)
    (h3 : CycleIntegralSection.Statement) (h4 : GreenSymmetry.Statement)
    (h5 : SupportCycleSection.Statement) : DefectSymm.Statement := by
  intro e hIH n δ h Z f u u' hZ hu hu' huu' hu'u

  have A := hIH n δ h (cycleSection Z u) (specFirst f u) u' (h1 n e δ Z f u hZ hu) huu'
  have B := hIH n δ h (cycleSection Z u') (specFirst f u') u (h1 n e δ Z f u' hZ hu') hu'u
  have S := h2 n e h Z f u u' hZ.chow

  obtain ⟨c, -, g, hg, -⟩ := hZ.chow
  have G : ∀ W ∈ Z.support,
      (Z W : ℝ) * (cycleIntegral h (divCycle W u) e (fsLog h u') + coneIntegral h W (e + 1) (fsLog h u)) =
        (Z W : ℝ) * (cycleIntegral h (divCycle W u') e (fsLog h u) +
          coneIntegral h W (e + 1) (fsLog h u')) := by
    intro W hW
    congr 1
    refine h4 n e h W u u' (hZ.prime W hW) ⟨g W, hg W hW⟩ (hu W hW) (hu' W hW) ?_
    intro W' hW'
    exact huu' W' ((h5 n Z u).1 W hW hW')
  have hsum := Finset.sum_congr rfl G
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have Cu := h3 n h Z u e (fsLog h u')
  have Cu' := h3 n h Z u' e (fsLog h u)
  have Ku : cycleIntegral h Z (e + 1) (fsLog h u) =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u) := rfl
  have Ku' : cycleIntegral h Z (e + 1) (fsLog h u') =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u') := rfl
  unfold mahlerDefect
  linarith
end

end GroundTheory.Heights₂.Heights
