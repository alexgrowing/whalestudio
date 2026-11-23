import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjDegreeChow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ProjDegreeChow.proof (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]

end

end GroundTheory.Heights₂.Heights
