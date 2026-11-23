import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula

namespace GlobalTheory.FlagCurve

theorem toForm_lamA_eq_two_mul_cross (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) :
    (toForm (lamA ι N j) : FormPol ι N) = 2 * ∑ s ∈ crSet ι N j, X s := by
  have key : ∀ τ : ι, (toForm (pHigh j τ 1 - pLow j τ 1) : FormPol ι N) =
      ∑ a : Fin N, ∑ b : Fin N,
        2 * (if a < b ∧ (a : ℕ) < j ∧ j ≤ (b : ℕ) then (X (τ, a, b) : FormPol ι N) else 0) := by
    intro τ
    have h1 : ∀ (p : Fin N → Prop) [DecidablePred p],
        ∑ i ∈ Finset.univ.filter p, (rootForm (τ, i) : FormPol ι N) =
          ∑ a : Fin N, ∑ b : Fin N,
            ((if p b then (if a < b then (X (τ, a, b) : FormPol ι N) else 0) else 0) -
              (if p a then (if a < b then (X (τ, a, b) : FormPol ι N) else 0) else 0)) := by
      intro p _
      simp only [Finset.sum_sub_distrib, Finset.sum_filter]
      rw [Finset.sum_comm (f := fun a b => if p b then (if a < b then (X (τ, a, b) : FormPol ι N) else 0) else 0),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p i <;> simp [hi, rootForm]
    simp only [toForm, pHigh, pLow, map_sub, map_sum, pow_one, aeval_X]
    rw [h1, h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a < b
    · have hab' : (a : ℕ) < b := hab
      by_cases ha : (a : ℕ) < j
      · by_cases hb : (b : ℕ) < j
        · simp [hab, ha, hb, not_le.mpr ha, not_le.mpr hb]
        · simp [hab, ha, hb, not_le.mpr ha, not_lt.mp hb, two_mul]
      · have hb : ¬ (b : ℕ) < j := by omega
        simp [hab, ha, hb, not_lt.mp ha, not_lt.mp hb]
    · simp [hab]
  have h2 : (toForm (lamA ι N j) : FormPol ι N) = ∑ τ : ι, toForm (pHigh j τ 1 - pLow j τ 1) := by
    simp only [lamA, toForm, map_sum]
  rw [h2, crSet, Finset.sum_filter, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, Fintype.sum_prod_type]

end GlobalTheory.FlagCurve
