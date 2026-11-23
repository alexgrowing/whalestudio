import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem copies_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧
    (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧
    ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  refine ⟨fun 𝒜 eps Fm => ⟨(working_classes_frozen.1 𝒜 eps Fm).2, (working_classes_frozen.1 𝒜 eps Fm).1⟩, fun eps Fm h => ?_⟩
  obtain ⟨a, b, c, d, e, f, g⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm h
  refine ⟨a, b, c, d, e, f, ?_⟩
  obtain ⟨x0, hx0⟩ := g
  exact ⟨x0, fun x hx hx1 i => hx0 x hx hx1 i⟩

end GlobalTheory.Fc
