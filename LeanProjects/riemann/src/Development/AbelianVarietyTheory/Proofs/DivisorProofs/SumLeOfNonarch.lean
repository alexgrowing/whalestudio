import Mathlib

namespace GlobalTheory.NonarchimedeanSumBound

theorem sum_le_of_nonarch {K : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean (⇑w : K → ℝ)) {ι : Type} (s : Finset ι) (f : ι → K) {c : ℝ}
    (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, (w : K → ℝ) (f i) ≤ c) :
    (w : K → ℝ) (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem main : ∀ {K : Type} [inst : Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean (⇑w : K → ℝ) → ∀ {ι : Type} (s : Finset ι) (f : ι → K) {c : ℝ}, (0 : ℝ) ≤ c → (∀ i ∈ s, (w : K → ℝ) (f i) ≤ c) → (w : K → ℝ) (∑ i ∈ s, f i) ≤ c :=
  fun w hw _ s f _ hc h => sum_le_of_nonarch w hw s f hc h

end GlobalTheory.NonarchimedeanSumBound
