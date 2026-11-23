import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat

section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem mul_zpow_mul_inv_pow_mul_zpow_lemma {G : Type*} [CommGroup G] (x y g : G) (k j a : ℤ)
    (M : ℕ) :
    (x * g ^ k) ^ a * ((y * g ^ j) ^ M)⁻¹ = x ^ a * (y ^ M)⁻¹ * g ^ (k * a - j * M) := by
  rw [mul_zpow, ← zpow_mul, mul_pow, ← zpow_natCast (g ^ j), ← zpow_mul, zpow_sub, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem dvrOrder_exists_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : R, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ 0 ≤ e := by
  have ht0 : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
  constructor
  · rintro ⟨r, hr⟩
    by_contra he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -((n + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
    have key : algebraMap R K (r * t ^ (n + 1)) = algebraMap R K v := by
      rw [map_mul, map_pow, hr, hn, zpow_neg, zpow_natCast, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]
    have hu : IsUnit (r * t ^ (n + 1)) := by
      rw [IsFractionRing.injective R K key]
      exact v.isUnit
    rw [pow_succ] at hu
    exact ht.1 (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu))
  · intro he
    lift e to ℕ using he
    exact ⟨v * t ^ e, by rw [map_mul, map_pow, zpow_natCast]⟩

theorem dvrOrder_exists_unit_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : Rˣ, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ e = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have ht0 : algebraMap R K t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
    have h1 : 0 ≤ e := (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht v e).1 ⟨r, hr⟩
    have h2 : 0 ≤ -e := by
      refine (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht r (-e)).1 ⟨v, ?_⟩
      rw [hr, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht0), mul_one]
    omega
  · rintro rfl
    exact ⟨v, by rw [zpow_zero, mul_one]⟩

end

theorem dvr_order_integral_unit_iff : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R) (s : K), ϖ ≠ 0 → ¬ IsUnit ϖ → s ≠ 0 → ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ), ((∃ r : R, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n ≤ a * m) ∧ ((∃ r : Rˣ, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n = a * m) := by
  intro R K _ _ _ _ _ _ ϖ s hϖ hϖu hs
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  obtain ⟨φ, hφ⟩ : ∃ φ : Rˣ →* Kˣ, ∀ x : Rˣ, ((φ x : Kˣ) : K) = algebraMap R K x :=
    ⟨Units.map (algebraMap R K).toMonoidHom, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, (g : K) = algebraMap R K π := ⟨Units.mk0 _ hπ0, rfl⟩
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ hπ
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      apply hϖu
      rw [hu, h, pow_zero, mul_one]
      exact u.isUnit
    · exact h
  have hϖK : algebraMap R K ϖ = algebraMap R K u * algebraMap R K π ^ (k : ℤ) := by
    rw [hu, map_mul, map_pow, zpow_natCast]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hs
    rw [← hxy, map_zero, zero_div]
  obtain ⟨i, w₁, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  obtain ⟨l, w₂, hy'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, w = w₁ * w₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (i : ℤ) - l := ⟨_, rfl⟩
  have hsK : s = algebraMap R K w * algebraMap R K π ^ j := by
    rw [← hxy, hx, hy', hw, hj]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_sub₀ hπ0, zpow_natCast]
    ring
  refine ⟨k, j, hk, fun M a => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, v = u ^ a * (w ^ M)⁻¹ := ⟨_, rfl⟩
  have hU : (φ u * g ^ (k : ℤ)) ^ a * ((φ w * g ^ j) ^ M)⁻¹ =
      φ v * g ^ ((k : ℤ) * a - j * M) := by
    rw [mul_zpow_mul_inv_pow_mul_zpow_lemma, hv, map_mul, map_zpow, map_inv, map_pow]
  have hU' := congrArg (fun z : Kˣ => (z : K)) hU
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, hφ, hg] at hU'
  have hX : ∀ r : K, r * s ^ M = algebraMap R K ϖ ^ a ↔
      r = algebraMap R K v * algebraMap R K π ^ ((k : ℤ) * a - j * M) := by
    intro r
    rw [← hU', ← hϖK, ← hsK, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hs)]
  constructor
  · rw [exists_congr fun r : R => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith
  · rw [exists_congr fun r : Rˣ => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_unit_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith

end GlobalTheory.CompanionTheory.Ar.Flat
