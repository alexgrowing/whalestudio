import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SetLIntegralLeOfMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.MtInvUpper

noncomputable section

open NumberField MeasureTheory

namespace PositivityTheory.KB.TwSMInt2

theorem sIntB : PositivityTheory.KB.SIntB := by
  intro L _ _ _ N hN μ _ M T B hB C hC f hf
  exact main_of_pack (ι := InfinitePlace L) hN μ (MomentRationality.Cz.Pk.cpt_Om M) T B
    (pack μ (MomentRationality.Cz.Pk.cpt_Om M) M T fun p hp w => ⟨hp.1 w, hp.2.1 w⟩) hB C hC f hf

end PositivityTheory.KB.TwSMInt2

end
