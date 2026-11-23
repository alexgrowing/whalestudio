import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartDenominatorAlt.equiv :
    GroundTheory.Heights₂.Heights.ChartDenominatorAlt.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartDenominatorAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D G Γ
    obtain ⟨hpos, hsmooth⟩ :=
      hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    rw [den_eq G Γ]
    exact ⟨hsmooth, hpos⟩
  · intro hB ι _ _ n P D d g h r f δ hf
    obtain ⟨hsmooth, hpos⟩ :=
      hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem h)
        (GenSystem.ofIsHomogGenerators hf)
    rw [den_ofFormSystem h hf]
    exact ⟨hpos, hsmooth⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
