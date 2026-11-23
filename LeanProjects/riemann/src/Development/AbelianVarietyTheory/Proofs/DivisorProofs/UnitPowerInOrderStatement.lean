import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPowerInOrder
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_power_in_order : ∀ (K F : Type) [CommRing K] [IsDomain K] [Module.Finite ℤ K] [Field F] [NumberField F] [Algebra K F] [IsFractionRing K F] (u : (𝓞 F)ˣ), ∃ e : ℕ, 0 < e ∧ ∃ a : Kˣ, algebraMap K F (a : K) = ((u : 𝓞 F) : F) ^ e := by
  first | exact @GlobalTheory.order_unit_pow_mem | exact GlobalTheory.order_unit_pow_mem | (intros; apply GlobalTheory.order_unit_pow_mem <;> assumption)
