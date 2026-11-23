import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.AnForm

noncomputable section

def LogLogCutHess.Statement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ), ∃ a b : ℝ,
    |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
    hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
    hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y

end

end GroundTheory.Heights₂.Heights
