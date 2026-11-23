import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
import Mathlib

namespace Bl.general_b_fact_upper_bis_form

theorem goal1 :
  ∀ {n : Nat} (f : Fin n → Rat),
  (∀ (i i' : Fin n), LT.lt.{0} i i' → LT.lt.{0} 0 (f i') → LT.lt.{0} 0 (f i)) →
    ∀ (i : Fin n), Iff (LT.lt.{0} 0 (f i)) (LT.lt.{0} i.val (PI.FJM.nP f))  := by
  intro n f hmono i
  unfold PI.FJM.nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.filter (fun j => 0 < f j) Finset.univ := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_eq_of_le hj with h | h
      · exact hmono j i h hi
      · rw [h]; exact hi
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hneg
    have hsub : Finset.filter (fun j => 0 < f j) Finset.univ ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      rw [not_lt] at hji
      rcases lt_or_eq_of_le hji with h | h
      · exact hneg (hmono i j h hj)
      · exact hneg (by rw [h]; exact hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_upper_bis_form
