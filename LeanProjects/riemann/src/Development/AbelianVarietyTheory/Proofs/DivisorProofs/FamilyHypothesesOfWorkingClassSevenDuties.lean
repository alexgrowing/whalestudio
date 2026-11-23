import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory.BigTop

theorem famHyp_of_working_duty : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps),
    GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  intro 𝒜 eps Fm hW hD
  obtain ⟨⟨⟨⟨_, hDvd, _, hBox, hQD, hCYL⟩, hSm⟩, hTw⟩, hCE, hTu, hDG⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm hD
  exact ⟨h1, h2, h3, h4, h5, hDvd, hBox, hQD, hCYL, hSm, hTw, hCE, hTu, hDG⟩

end GlobalTheory.BigTop
