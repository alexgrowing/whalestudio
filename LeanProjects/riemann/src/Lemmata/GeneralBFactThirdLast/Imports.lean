import Mathlib

namespace Bl.general_b_fact_third_last

theorem goal1 :
  ∀ {a : WithBot.{0} ENat} {n : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} a 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} n 1)) → Eq.{1} a (Nat.cast.{0} n) := by
  intro a n h
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact WithBot.bot_ne_coe h
  | coe e =>
    have h1 : ((e + 1 : ENat) : WithBot ENat) = (((n : ENat) + 1 : ENat) : WithBot ENat) := by
      rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast, h]
      push_cast
      rfl
    have h2 : e + 1 = (n : ENat) + 1 := WithBot.coe_injective h1
    have h3 : e = (n : ENat) := ENat.add_left_injective_of_ne_top ENat.one_ne_top h2
    rw [h3, WithBot.coe_natCast]

end Bl.general_b_fact_third_last
