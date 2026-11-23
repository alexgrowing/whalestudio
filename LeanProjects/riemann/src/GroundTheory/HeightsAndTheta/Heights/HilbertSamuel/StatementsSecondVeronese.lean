import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SecondVeronese.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (κ : Type) (_ : Fintype κ) (d : HSMDatum D Ω κ),
      (∀ n : ℕ, resChi d n = chiP D (2 * n)) ∧
      (∀ I : AllFam, I.IsFamily → top I d.x d.m D = 2 ^ (D + 1) * hhOf I D) ∧
      genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = 2 ^ D

example : (1 : ℕ) ≤ 1 := le_rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
