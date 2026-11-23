import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegreeIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

theorem BlockResolutionDegree.proof (hRank : BlockSectionsRank.Statement)
    (hInt : BlockResolutionDegreeIntegral.Statement) : BlockResolutionDegree.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h₀ h₁ s₀ s₁ t ht
  obtain ⟨C, hC⟩ := hRank D K ι Ω d.y d.k₀ d.one_le d.arith d.birat
  refine ⟨C, fun n => ?_⟩
  rw [hInt D K ι Ω d A₀ A₁ h₀ h₁ s₀ s₁ t ht]
  exact hC n

end GroundTheory.Heights₂.Heights.HilbertSamuel
