import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula

namespace GlobalTheory.FlagCurve

theorem toForm_pLow_one (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ : ι) :
    (toForm (pLow j τ 1 : Pol ι N) : FormPol ι N) =
      -∑ s ∈ (crSet ι N j).filter (fun s => s.1 = τ), X s := by
  have h1 : ∑ s ∈ (crSet ι N j).filter (fun s => s.1 = τ), (X s : FormPol ι N) =
      ∑ a : Fin N, ∑ b : Fin N,
        if a < b ∧ (a : ℕ) < j ∧ j ≤ (b : ℕ) then X (τ, a, b) else 0 := by
    rw [crSet, Finset.filter_filter, Finset.sum_filter, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [and_true]
    · intro t _ ht
      simp [ht]
    · simp
  rw [h1, toForm, pLow, map_sum, Finset.sum_filter]
  simp only [pow_one, aeval_X, rootForm]
  have h2 : ∀ i : Fin N, (if (i : ℕ) < j then
      ((∑ a : Fin N, if a < i then X (τ, a, i) else 0) -
        ∑ b : Fin N, if i < b then X (τ, i, b) else 0 : FormPol ι N) else 0) =
      (∑ a : Fin N, if a < i ∧ (i : ℕ) < j then X (τ, a, i) else 0) -
        ∑ b : Fin N, if i < b ∧ (i : ℕ) < j then X (τ, i, b) else 0 := by
    intro i
    by_cases h : (i : ℕ) < j <;> simp [h]
  simp only [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a < b
  · have hab' : (a : ℕ) < b := hab
    by_cases hb : (b : ℕ) < j
    · have ha : (a : ℕ) < j := by omega
      simp [hab, hb, ha, not_le.mpr hb]
    · by_cases ha : (a : ℕ) < j
      · simp [hab, hb, ha, not_lt.mp hb]
      · simp [hb, ha]
  · simp [hab]

end GlobalTheory.FlagCurve
