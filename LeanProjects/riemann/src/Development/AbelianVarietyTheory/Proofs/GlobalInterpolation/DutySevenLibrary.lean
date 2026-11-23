import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightAdmissibleSmallSharesAtPoint

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

theorem duty_seven_library : ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → Formalism.MainNotions.PageFix Fm ∧ Formalism.MainNotions.PageWin Fm ∧
    Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.ChosenWall Fm ∧ DQ.TupUsedF Fm ∧ DQ.TwAllF Fm := by
  intro eps Fm h
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  refine ⟨a, b, fun x hx i => (c x hx i).2.2.2.2.1, ?_, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, f, g⟩
  · unfold DC.TameDistinctF at d
    unfold Formalism.MainNotions.TameDistinctF
    simpa only [tameDistinct_iff] using d
  · exact weightAdmissible_smallShares_at_point _ _ (e x (by linarith) i)

end GlobalTheory.EX.DQ
