import Mathlib

namespace Bl.FirstBlockLemmaI

theorem goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] {u z : R},
  IsUnit.{0} u → Membership.mem.{0, 0} (Ideal.jacobson.{0} Bot.bot.{0}) z → IsUnit.{0} (HAdd.hAdd.{0, 0, 0} u z) := by
  intro R _ u z hu hz
  obtain ⟨v, rfl⟩ := hu
  have h := (Ideal.mem_jacobson_bot.mp hz) (↑v⁻¹ : R)
  have e : (v : R) + z = (z * ↑v⁻¹ + 1) * ↑v := by
    rw [add_mul, one_mul, mul_assoc, Units.inv_mul, mul_one, add_comm]
  rw [e]
  exact h.mul v.isUnit

end Bl.FirstBlockLemmaI
