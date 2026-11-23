import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def WeierstrassPolynomialDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (c : Fin d → (σ → ℂ) → ℂ) (g : (Option σ → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (c j) 0) → (∀ j, c j 0 = 0) → AnalyticAt ℂ g 0 →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * weierstrassPolynomial c x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
