import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem trunc'_eval_dvd_of_order :
    ∀ (p : ℕ) (B : Type) [CommRing B] (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B),
      (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∃ L : ℕ, ∀ (k : ℕ) (h : MvPowerSeries σ B),
        (∀ α : σ →₀ ℕ, α.degree < L * k → coeff α h = 0) →
          ∀ n : σ →₀ ℕ, (p : B) ^ k ∣ MvPolynomial.eval z (trunc' B n h) := by
  intro p B _ σ _ _ z hz
  choose N hN using hz
  set N₀ : ℕ := ∑ i, N i + 1 with hN₀
  have hdiv : ∀ i, (p : B) ∣ z i ^ N₀ := by
    intro i
    have hle : N i ≤ N₀ := by
      have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    exact (hN i).trans (pow_dvd_pow _ hle)
  refine ⟨Fintype.card σ * N₀ + 1, ?_⟩
  intro k h hh n
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [MvPolynomial.eval_eq]
  apply Finset.dvd_sum
  intro β _
  rw [coeff_trunc']
  split_ifs with hβ
  · by_cases hc : coeff β h = 0
    · simp [hc]
    · have hdeg : ¬ β.degree < (Fintype.card σ * N₀ + 1) * k := fun hlt => hc (hh β hlt)
      have : ∃ i, N₀ * k ≤ β i := by
        by_contra hne
        push_neg at hne
        apply hdeg
        rw [Finsupp.degree_eq_sum]
        calc ∑ i, β i ≤ ∑ _i : σ, N₀ * k := Finset.sum_le_sum (fun i _ => (hne i).le)
          _ = Fintype.card σ * N₀ * k := by simp [Finset.sum_const, mul_assoc]
          _ < (Fintype.card σ * N₀ + 1) * k := by nlinarith
      obtain ⟨i, hi⟩ := this
      apply Dvd.dvd.mul_left
      have h1 : (p : B) ^ k ∣ z i ^ β i := by
        calc (p : B) ^ k ∣ (z i ^ N₀) ^ k := pow_dvd_pow_of_dvd (hdiv i) k
          _ = z i ^ (N₀ * k) := (pow_mul _ _ _).symm
          _ ∣ z i ^ β i := pow_dvd_pow _ hi
      have hmem : i ∈ β.support := by
        rw [Finsupp.mem_support_iff]
        have : 1 ≤ N₀ * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        omega
      exact h1.trans (Finset.dvd_prod_of_mem _ hmem)
  · simp

end GlobalTheory
