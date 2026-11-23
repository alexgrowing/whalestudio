import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsFurther
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaAndWindowCount

namespace GlobalTheory.ThinScaleLiterature

theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
