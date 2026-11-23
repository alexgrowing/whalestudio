import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExists

noncomputable section

namespace PI.WA

open PI.WADVR

section Field

variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}

lemma g_big_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hqs : Sm Q ϖ 1 q⁻¹) (hY : Sm Q ϖ 1 Y⁻¹)
    (r : ℕ) : Sm Q ϖ 1 (q ^ r * Y)⁻¹ := by
  have h1 := (Sm.pow hϖ hqs r).mul hϖ hY
  rw [mul_inv, ← inv_pow]
  exact h1.mono hϖ (by push_cast; omega)

lemma g_small_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y)
    (r : ℕ) (hr : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * Y) :=
  ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)

lemma g_int_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 0 q) (hY : Sm Q ϖ 1 Y) (r : ℕ) :
    Sm Q ϖ 1 (q ^ r * Y) := by
  exact ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)

lemma g_B_big (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹) (hY0 : Y ≠ 0)
    (hY : Sm Q ϖ 1 Y⁻¹) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, -⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  refine ⟨h1, ?_⟩
  have e : (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ = (1 + (q⁻¹) ^ r) * Y⁻¹ := by
    rw [inv_pow]
    field_simp
    ring
  rw [e]
  have h2 : Sm Q ϖ 0 (1 + (q⁻¹) ^ r) := Sm.add Sm.one (ht.mono hϖ (by norm_num))
  have h3 := h2.mul hϖ hY
  simpa using h3

lemma g_B_small (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y) {r : ℕ}
    (hr : 1 ≤ r) (hrm : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have hqr := Sm.pow hϖ hq r
  obtain ⟨-, hinv⟩ := one_add_of_sm hϖ (hqr.mono hϖ (by push_cast; omega))
  exact ((hqr.mul hϖ hinv).mul hϖ hY).mono hϖ (by push_cast; omega)

lemma g_B_bigj (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹)
    (hY : Sm Q ϖ 1 Y) {r : ℕ} (hr : 1 ≤ r) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, hinv⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  have e : q ^ r * (1 + q ^ r)⁻¹ = (1 + (q⁻¹) ^ r)⁻¹ := by
    rw [inv_pow, eq_comm, inv_eq_iff_eq_inv, mul_inv, inv_inv, mul_add, inv_mul_cancel₀ hqr, mul_one,
      add_comm]
  rw [e]
  simpa using hinv.mul hϖ hY

end Field

theorem big_existence_holds : BigExists := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden hdist ϖ hϖ i
  classical

  have pair : ∀ j, j ≠ i → ∃ y : E, y ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i y)⁻¹ ∧
      Sm (Q j) (ϖ j) 1 (iw j y) := by
    intro j hji
    obtain ⟨a, haj, hai⟩ := hdist j i hji
    obtain ⟨b, hbi, hbj⟩ := hdist i j (Ne.symm hji)
    obtain ⟨hai0, hai1⟩ := big_of_not_mem (hϖ i) hai
    obtain ⟨hbj0, hbj1⟩ := big_of_not_mem (hϖ j) hbj
    have ha0 : a ≠ 0 := fun h => hai0 (by rw [h, map_zero])
    have hb0 : b ≠ 0 := fun h => hbj0 (by rw [h, map_zero])
    refine ⟨a * b⁻¹, mul_ne_zero ha0 (inv_ne_zero hb0), ?_, ?_⟩
    · have e : (iw i (a * b⁻¹))⁻¹ = iw i b * (iw i a)⁻¹ := by
        rw [map_mul, map_inv₀, mul_inv, inv_inv, mul_comm]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ i)).mpr hbi).mul (hϖ i) hai1
      rwa [zero_add] at this
    · have e : iw j (a * b⁻¹) = iw j a * (iw j b)⁻¹ := by rw [map_mul, map_inv₀]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ j)).mpr haj).mul (hϖ j) hbj1
      rwa [zero_add] at this

  have base : ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ := by
    obtain ⟨a, c, hac⟩ := hden i ((p : Q i)⁻¹) 1
    have hpi := hp0 i
    have hts : Sm (Q i) (ϖ i) 1 ((p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      have h1 := ((sm_natCast (Q := Q i) (hϖ i) (hpu i)).pow (hϖ i) 2).mul (hϖ i)
        (Sm.alg (ϖ := ϖ i) (Q := Q i) c)
      exact h1.mono (hϖ i) (by norm_num)
    obtain ⟨h1t, h2t⟩ := one_add_of_sm (hϖ i) hts
    have e : iw i a = (p : Q i)⁻¹ * (1 + (p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      rw [hac]
      field_simp
    refine ⟨a, fun h => ?_, ?_⟩
    · rw [h, map_zero] at e
      exact mul_ne_zero (inv_ne_zero hpi) h1t e.symm
    · rw [e, mul_inv, inv_inv]
      have := (sm_natCast (Q := Q i) (hϖ i) (hpu i)).mul (hϖ i) h2t
      rwa [add_zero] at this

  have main : ∀ S : Finset ι, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧
      ∀ k ∈ S, k ≠ i → Sm (Q k) (ϖ k) 1 (iw k z) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz, hzi⟩ := base
      exact ⟨z, hz, hzi, by simp⟩
    | @insert j S hjS ih =>
      obtain ⟨z, hz0, hzi, hzS⟩ := ih
      by_cases hji : j = i
      · refine ⟨z, hz0, hzi, fun k hk hki => hzS k ?_ hki⟩
        exact (Finset.mem_insert.mp hk).resolve_left (fun h => hki (h.trans hji))
      · obtain ⟨y, hy0, hyi, hyj⟩ := pair j hji
        choose m hm using fun k => sm_exists (hϖ k) (iw k y)
        obtain ⟨r, hr1, hrm⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ k, 1 ≤ (r : ℤ) + m k := by
          refine ⟨1 + ∑ k, (-(m k)).toNat, by omega, fun k => ?_⟩
          have h1 : (-(m k)).toNat ≤ ∑ k, (-(m k)).toNat :=
            Finset.single_le_sum (f := fun k => (-(m k)).toNat) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
          have h2 := Int.self_le_toNat (-(m k))
          have h3 : ((1 + ∑ k, (-(m k)).toNat : ℕ) : ℤ) ≥ 1 + ((-(m k)).toNat : ℤ) := by
            exact_mod_cast Nat.add_le_add_left h1 1
          linarith
        have hzi0 : iw i z ≠ 0 := (map_ne_zero _).mpr hz0
        by_cases hzj : iw j z ∈ Set.range (algebraMap (W j) (Q j))
        · refine ⟨z ^ r * y, mul_ne_zero (pow_ne_zero _ hz0) hy0, ?_, ?_⟩
          · rw [map_mul, map_pow]
            exact g_big_pow_mul (hϖ i) hzi hyi r
          · intro k hk hki
            rw [map_mul, map_pow]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_int_pow_mul (hϖ j) ((sm_zero_iff (ϖ := ϖ j)).mpr hzj) hyj r
            · exact g_small_pow_mul (hϖ k) (hzS k hkS hki) (hm k) r (hrm k)
        · obtain ⟨hzj0, hzj1⟩ := big_of_not_mem (hϖ j) hzj
          obtain ⟨hd, hbig⟩ := g_B_big (hϖ i) hzi0 hzi ((map_ne_zero _).mpr hy0) hyi hr1
          have hmap : ∀ k, iw k (z ^ r * (1 + z ^ r)⁻¹ * y) =
              (iw k z) ^ r * (1 + (iw k z) ^ r)⁻¹ * iw k y := fun k => by
            simp only [map_mul, map_pow, map_inv₀, map_add, map_one]
          have hd' : (1 + z ^ r : E) ≠ 0 := fun h => hd (by
            have : iw i (1 + z ^ r) = 1 + (iw i z) ^ r := by
              simp only [map_add, map_one, map_pow]
            rw [← this, h, map_zero])
          refine ⟨z ^ r * (1 + z ^ r)⁻¹ * y,
            mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hd')) hy0, ?_, ?_⟩
          · rw [hmap]
            exact hbig
          · intro k hk hki
            rw [hmap]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_B_bigj (hϖ j) hzj0 hzj1 hyj hr1
            · exact g_B_small (hϖ k) (hzS k hkS hki) (hm k) hr1 (hrm k)
  obtain ⟨z, hz0, hzi, hzS⟩ := main Finset.univ
  exact ⟨z, hz0, hzi, fun j hj => hzS j (Finset.mem_univ j) hj⟩

end PI.WA
