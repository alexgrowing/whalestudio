import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.exists_limit_of_successive_diff_mem_filtration :
    ∀ (P : Type) [CommRing P] (m : Ideal P) [IsPrecomplete m P] (J : ℕ → Ideal P), (∀ N, m ^ (N + 1) ≤ J N) → (∀ N, J N ≤ J (N + 1) ⊔ m ^ (N + 1)) → ∀ (N₀ : ℕ) (p : ℕ → P), (∀ N, N₀ ≤ N → p (N + 1) - p N ∈ J N) → ∃ x : P, (∀ N, N₀ ≤ N → x - p N ∈ J N) ∧ x - p N₀ ∈ m ^ (N₀ + 1) := by
  intro P _ m _ J hmJ hJ N₀ p hp
  classical
  have hsm : ∀ n, (m ^ n • ⊤ : Submodule P P) = m ^ n := by
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have step : ∀ (k : ℕ) (y : P), ∃ y' : P,
      y - p (N₀ + k) ∈ J (N₀ + k) →
        y' - p (N₀ + k + 1) ∈ J (N₀ + k + 1) ∧ y' - y ∈ m ^ (N₀ + k + 1) := by
    intro k y
    by_cases hy : y - p (N₀ + k) ∈ J (N₀ + k)
    · have h1 : y - p (N₀ + k + 1) ∈ J (N₀ + k) := by
        have h := sub_mem hy (hp (N₀ + k) (Nat.le_add_right _ _))
        have e : y - p (N₀ + k + 1) = y - p (N₀ + k) - (p (N₀ + k + 1) - p (N₀ + k)) := by ring
        rw [e]
        exact h
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 (hJ (N₀ + k) h1)
      refine ⟨y - t, fun _ => ⟨?_, ?_⟩⟩
      · have e : y - t - p (N₀ + k + 1) = j := by
          rw [sub_right_comm, ← hjt]
          ring
        rw [e]
        exact hj
      · rw [sub_sub_cancel_left]
        exact neg_mem ht
    · exact ⟨y, fun h => absurd h hy⟩
  choose g hg using step
  let q : ℕ → P := fun k => Nat.rec (p N₀) (fun k y => g k y) k
  have hq0 : q 0 = p N₀ := rfl
  have hqs : ∀ k, q (k + 1) = g k (q k) := fun k => rfl
  have hqJ : ∀ k, q k - p (N₀ + k) ∈ J (N₀ + k) ∧ q (k + 1) - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    induction k with
    | zero =>
      have h0 : q 0 - p (N₀ + 0) ∈ J (N₀ + 0) := by simp [hq0]
      exact ⟨h0, by rw [hqs]; exact (hg 0 (q 0) h0).2⟩
    | succ k ih =>
      have h0 : q (k + 1) - p (N₀ + (k + 1)) ∈ J (N₀ + (k + 1)) := by
        rw [hqs]
        exact (hg k (q k) ih.1).1
      exact ⟨h0, by rw [hqs (k + 1)]; exact (hg (k + 1) (q (k + 1)) h0).2⟩
  have hcau : ∀ a b, a ≤ b → q b - q a ∈ m ^ (N₀ + a + 1) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h := add_mem (Ideal.pow_le_pow_right (by omega) (hqJ b).2) ih
      rwa [sub_add_sub_cancel] at h
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := m) q (fun {a b} hab => by
    rw [hsm, SModEq.sub_mem, ← neg_sub]
    exact neg_mem (Ideal.pow_le_pow_right (by omega) (hcau a b hab)))
  have hx : ∀ k, L - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    have h1 := hL (N₀ + k + 1)
    rw [hsm, SModEq.sub_mem] at h1
    have h2 := hcau k (N₀ + k + 1) (by omega)
    have e : L - q k = -(q (N₀ + k + 1) - L) + (q (N₀ + k + 1) - q k) := by ring
    rw [e]
    exact add_mem (neg_mem h1) h2
  refine ⟨L, fun N hN => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have e : L - p (N₀ + k) = (L - q k) + (q k - p (N₀ + k)) := by ring
    rw [e]
    exact add_mem (hmJ (N₀ + k) (hx k)) (hqJ k).1
  · simpa [hq0] using hx 0
