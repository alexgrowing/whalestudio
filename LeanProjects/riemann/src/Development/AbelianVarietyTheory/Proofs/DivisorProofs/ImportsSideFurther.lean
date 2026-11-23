import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

namespace GlobalTheory.FourClauses

theorem len : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.StandardFunctorsFiniteLength :=
  fun h k _ _ _ _ _ _ _ => ⟨fun V _ _ π hs hl => (h k).2.1 _ _ _ _ V π hs hl, fun W _ _ ρ hs hl => (h k).2.2.1 _ _ _ _ W ρ hs hl⟩

end GlobalTheory.FourClauses
