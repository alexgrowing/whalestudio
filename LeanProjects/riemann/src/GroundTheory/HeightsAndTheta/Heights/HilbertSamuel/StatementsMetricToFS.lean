import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def MetricToFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    ∃ d₀ : HSMDatum D Ω κ, d₀.x = d.x ∧ IsPullFS d.x e d₀.m ∧
      (fun n => hsDefect D (resChi d₀) (top I d.x d₀.m D) n - hsDefect D (resChi d) (top I d.x d.m D) n)
        =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
