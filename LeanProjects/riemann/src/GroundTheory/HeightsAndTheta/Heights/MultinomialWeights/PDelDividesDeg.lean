import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial

theorem degPoly_isBlockAlternating (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement)
    (d : IndexData) : RestTerms.IsBlockAlternating d.f d.N (degPoly d) := by
  intro w
  apply MvPolynomial.funext
  intro u
  have h := hAnti d w u
  rw [← hEval, ← hEval] at h
  rw [RestTerms.blockPermute, eval_rename, smul_eval]
  exact h

theorem DelDividesDeg.proof (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement) :
    DelDividesDeg.Statement := fun d =>
  RestTerms.FlagVandermondeDvd.full d.f d.N (degPoly d) (degPoly_isBlockAlternating hAnti hEval d)

end GroundTheory.Heights₂.Heights.TheoremB
