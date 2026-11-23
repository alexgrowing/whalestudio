import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem frobQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ x : Qr p r, (⇑(frobQ p r))^[r] x = x := by
  intro p _ r hr x
  have h : (⇑(frobQ p r) : Qr p r → Qr p r) = ⇑(GlobalTheory.LKLoc.frobR p (Q0 p) r) := rfl
  rw [h]
  exact GlobalTheory.LKLoc.frobR_iterate_self p (Q0 p) (by infer_instance) r hr x

end GlobalTheory.LKRes
