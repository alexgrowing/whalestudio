import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeEuclMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem TubeEuclMass.proof (hC : TubeCollarMass.Statement) (hD : TubeDeepMass.Statement) :
    TubeEuclMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hS : {y : Fin (d + 1) → ℂ | logAbsSq P y < -Real.exp 1} =
      {y | -Real.exp 1 ≤ logAbsSq P y}ᶜ := by
    ext y
    simp [not_le]
  have h := (hC n d J A P R hJ hdim hA hP).add (hD n d J A P R hJ hdim hA hP)
  rw [hS, Set.indicator_self_add_compl] at h
  exact h

end

end GroundTheory.Heights₂.Heights
