import Mathlib

theorem UpperTheory.V.Th.fNil :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  simp only [not_forall] at hne
  obtain ⟨i, i', hii', hα⟩ := hne
  have hcase : (U i - U i') ^ (2 * N) = 0 ∨ (U i - (q : S) * U i') ^ (2 * N) = 0 := by
    have ha : (U i - f (α i)) ^ N = 0 := hU i
    have hb : (U i' - f (α i')) ^ N = 0 := hU i'
    by_cases he : α i = α i'
    · left
      have hnb : (-(U i' - f (α i'))) ^ N = 0 := by rw [neg_pow, hb, mul_zero]
      have hx : U i - U i' = (U i - f (α i)) + -(U i' - f (α i')) := by
        rw [he]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
    · right
      have hq : α i = (q : K) * α i' := by
        by_contra h'
        exact hα ⟨he, h'⟩
      have hnb : (-(q : S) * (U i' - f (α i'))) ^ N = 0 := by rw [mul_pow, hb, mul_zero]
      have hx : U i - (q : S) * U i' = (U i - f (α i)) + -(q : S) * (U i' - f (α i')) := by
        rw [hq, map_mul, map_natCast]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
  have hY : ((U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
    rw [mul_pow]
    rcases hcase with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  have hdvd : (U i - U i') * (U i - (q : S) * U i') ∣
      ∏ j : Fin n, ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j') :=
    (Finset.dvd_prod_of_mem (fun j' => (U i - U j') * (U i - (q : S) * U j'))
      (Finset.mem_erase.2 ⟨hii'.symm, Finset.mem_univ _⟩)).trans
      (Finset.dvd_prod_of_mem
        (fun j => ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j'))
        (Finset.mem_univ i))
  exact zero_dvd_iff.1 (hY ▸ pow_dvd_pow_of_dvd hdvd (2 * N))
