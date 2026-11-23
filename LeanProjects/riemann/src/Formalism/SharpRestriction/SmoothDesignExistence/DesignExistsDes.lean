import Formalism.SharpRestriction.MuTuOfTuSize
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Pk

abbrev Des (𝒞 : FamClass) (C0 : ℝ) : FamClass :=
  fun Fm => ((𝒞 Fm ∧ DGamSmooth Fm) ∧ TwGood Fm) ∧ (∃ CH : ℝ, ChosenE Fm C0 CH) ∧ TuSize Fm ∧ DGamSize Fm

abbrev WithSm (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ DGamSmooth Fm

end Formalism.MainNotions

end
