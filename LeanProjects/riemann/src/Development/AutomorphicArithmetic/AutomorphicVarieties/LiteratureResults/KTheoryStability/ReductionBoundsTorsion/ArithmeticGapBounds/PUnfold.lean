import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PUnfoldA
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PUnfoldB

namespace PositivityTheory.KB.SpectralGap

theorem unfold_holds : Unfold := by
  intro Λ S _ _ _ _ _ μ _ j hj B K hBK hi
  exact ⟨fun u hu => UnfoldA.avg_linv j B K hi u hu, fun u hu => UnfoldA.avg_of_linv j B K hi u hu,
    fun u hu => UnfoldA.avg_meas j B K hi u hu,
    fun E hBE hEK u hu => UnfoldA.avg_tower j B E K hBE hEK hi u hu,
    UnfoldB.unfold_fd Λ S μ j hj B K hBK hi⟩

end PositivityTheory.KB.SpectralGap
