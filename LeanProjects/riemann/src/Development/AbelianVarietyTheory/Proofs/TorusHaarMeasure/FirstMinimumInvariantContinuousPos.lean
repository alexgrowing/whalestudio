import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FirstMinimum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmType_nonempty {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have h' : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
      by_contra h2
      exact h ((X.cmType τ).mpr h2)
    exact ⟨⟨_, h'⟩⟩

omit [NumberField E] [IsCMField E] in
theorem emb_mulVec {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M.mulVec v) = (M.map τ).mulVec (Data.emb τ v) := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.FirstMinimum
