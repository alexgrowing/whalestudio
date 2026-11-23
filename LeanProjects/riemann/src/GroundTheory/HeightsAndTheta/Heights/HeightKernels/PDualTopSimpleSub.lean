import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSimpleSub.proof (hBasis : DualTopBasisChange.Statement)
    (hStep : DualTopSimpleStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSimpleSub.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hlt hcov
  have hle := hlt.le
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStep K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hlt hcov hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
