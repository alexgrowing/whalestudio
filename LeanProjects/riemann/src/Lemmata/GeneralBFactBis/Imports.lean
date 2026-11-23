import Mathlib

namespace Bl.general_b_fact_bis

theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact absurd h.symm WithBot.coe_ne_bot
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, WithBot.coe_inj]
    induction e using ENat.recTopCoe with
    | top =>
      rw [top_add] at h
      exact absurd h.symm (ENat.natCast_ne_top _)
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_inj] at h
      rw [ENat.natCast_inj]
      omega

end Bl.general_b_fact_bis
