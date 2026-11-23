import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps

open FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

theorem posPart_pw (a : List ℤ) (ha : a.Pairwise (· ≥ ·)) : (PI.FJM.posPart a).Pairwise (· ≥ ·) := by
  rw [PI.FJM.posPart, List.pairwise_map]
  exact ha.imp fun h => by omega

theorem negPart_pw (b : List ℤ) (hb : b.Pairwise (· ≥ ·)) : (PI.FJM.negPart b).Pairwise (· ≥ ·) := by
  rw [PI.FJM.negPart, List.pairwise_reverse, List.pairwise_map]
  exact hb.imp fun h => by omega

theorem posPart_getD (a : List ℤ) (ha : ∀ v ∈ a, 0 < v) (i : ℕ) :
    ((PI.FJM.posPart a).getD i 0 : ℚ) = if h : i < a.length then ((a[i] : ℤ) : ℚ) else 0 := by
  by_cases h : i < a.length
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.posPart] using h)]
    simp only [PI.FJM.posPart, List.getElem_map]
    have hpos := ha _ (List.getElem_mem h)
    have := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa [PI.FJM.posPart] using not_lt.1 h)]
    simp

theorem negPart_getD (b : List ℤ) (hb : ∀ v ∈ b, v < 0) (j : ℕ) :
    ((PI.FJM.negPart b).getD j 0 : ℚ) =
      if h : j < b.length then -((b[b.length - 1 - j]'(by omega) : ℤ) : ℚ) else 0 := by
  by_cases h : j < b.length
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.negPart] using h)]
    simp only [PI.FJM.negPart, List.getElem_reverse, List.getElem_map, List.length_map]
    have hneg := hb _ (List.getElem_mem (l := b) (n := b.length - 1 - j) (by omega))
    have := Int.toNat_of_nonneg (show 0 ≤ -b[b.length - 1 - j] by omega)
    have h2 : ((-b[b.length - 1 - j]).toNat : ℚ) = ((-b[b.length - 1 - j] : ℤ) : ℚ) := by
      exact_mod_cast this
    rw [h2]
    push_cast
    ring
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa [PI.FJM.negPart] using not_lt.1 h)]
    simp

theorem pad_getD (a b : List ℤ) (n : ℕ) (hn : a.length + b.length ≤ n) (ha : ∀ v ∈ a, 0 < v)
    (hb : ∀ v ∈ b, v < 0) (i : ℕ) (hi : i < n) :
    (pad a (n - a.length - b.length) b).getD i 0 =
      ((PI.FJM.posPart a).getD i 0 : ℚ) - ((PI.FJM.negPart b).getD (n - 1 - i) 0 : ℚ) := by
  rw [posPart_getD a ha, negPart_getD b hb]
  rw [pad, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map]
  by_cases h1 : i < a.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1,
      dif_pos h1, dif_neg (by omega)]
    simp
  · by_cases h2 : i < a.length + (n - a.length - b.length)
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
        dif_neg h1, dif_neg (by omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega), dif_neg h1, dif_pos (by omega)]
      simp only [neg_neg, sub_neg_eq_add, zero_add]
      congr 2
      simp
      omega

end PI.FJMX
