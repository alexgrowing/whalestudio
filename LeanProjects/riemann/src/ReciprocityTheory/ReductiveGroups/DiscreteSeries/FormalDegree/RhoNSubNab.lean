import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Finrank

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def nab (ε : Fin n → Bool) (a b : Fin n) : ℕ := (univ.filter fun c : Fin n => a < c ∧ c < b ∧ ε c ≠ ε a).card

theorem rhoN_sub_nab (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    rhoN ε a - rhoN ε b = (nab ε a b : ℝ) := by
  unfold rhoN nab
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have key : ∀ c : Fin n,
      ((if a < c ∧ ε c ≠ ε a then (1:ℝ) else 0) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if b < c ∧ ε c ≠ ε b then 1 else 0) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) =
      2 * (if a < c ∧ c < b ∧ ε c ≠ ε a then 1 else 0) := by
    intro c
    by_cases hc : ε c = ε a
    · have hcb : ε c = ε b := hc.trans he
      simp [hc, hcb, he]
    · have hcb : ε c ≠ ε b := fun h => hc (h.trans he.symm)
      rcases lt_trichotomy c a with h1 | h1 | h1
      · have h2 : c < b := h1.trans hab
        simp [hc, hcb, h1, h2, not_lt.mpr h1.le, not_lt.mpr h2.le] <;> norm_num
      · subst h1
        exact absurd rfl hc
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · simp [hc, hcb, h1, h3, not_lt.mpr h1.le, not_lt.mpr h3.le] <;> norm_num
        · subst h3
          exact absurd he.symm hc
        · have h4 : a < c := hab.trans h3
          simp [hc, hcb, h1, h3, h4, not_lt.mpr h1.le, not_lt.mpr h3.le] <;> norm_num
  have hsum := Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) => key c)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

theorem lemma7 {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) :
    (Module.finrank ℂ T.V : ℝ) =
      (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (lam a - lam b + (nab ε a b : ℝ))) /
        ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ)) := by
  rw [HW.hwfin_weyl T]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have h := rhoN_sub_nab ε hb.1 hb.2
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    linarith

end ReciprocityTheory.ChartRestriction.DS
