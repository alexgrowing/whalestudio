import Mathlib
open PowerSeries

namespace GlobalTheory.PadicUnitGen

theorem dvd_iff_toZMod {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem one_add_pow_eq {R : Type*} [CommRing R] (t : R) (j : ℕ) :
    ∃ z, (1 + t) ^ j = 1 + j * t + t ^ 2 * z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨j + z + t * z, by rw [pow_succ, hz]; push_cast; ring⟩

theorem exists_pow_approx {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]) (h2 : l ≠ 2)
    (hu : Associated (u - 1) (l : ℤ_[l])) (x : ℤ_[l]) (hx : (l : ℤ_[l]) ∣ x - 1) (k : ℕ) :
    ∃ m : ℕ, (l : ℤ_[l]) ^ (k + 1) ∣ x - u ^ m := by
  obtain ⟨w, hw⟩ := hu.symm
  have hu' : u = 1 + l * (w : ℤ_[l]) := by rw [hw]; ring
  have h3 : 3 ≤ l := by
    have := hl.out.two_le
    omega
  have hl0 : PadicInt.toZMod (l : ℤ_[l]) = 0 := by simp
  have hw0 : PadicInt.toZMod (w : ℤ_[l]) ≠ 0 :=
    (w.isUnit.map (PadicInt.toZMod (p := l))).ne_zero
  have hu1 : PadicInt.toZMod u = 1 := by rw [hu']; simp
  induction k with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨m, c, hc⟩ := ih
    obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := l) (v := l)
      hl.out dvd_rfl (by rw [← pow_two, ← pow_succ]; exact pow_dvd_pow _ h3) (w : ℤ_[l]) k
    rw [← hu'] at hy
    set j : ℕ := (PadicInt.toZMod c / PadicInt.toZMod (w : ℤ_[l])).val with hj
    obtain ⟨z, hz⟩ := one_add_pow_eq ((l : ℤ_[l]) ^ k * l * (w + l * y)) j
    refine ⟨m + l ^ k * j, ?_⟩
    have hd : (l : ℤ_[l]) ∣ c - u ^ m * (j * (w + l * y)
        + (l : ℤ_[l]) ^ k * l * (w + l * y) ^ 2 * z) := by
      rw [dvd_iff_toZMod]
      simp only [map_sub, map_mul, map_add, map_pow, hl0, hu1, map_natCast, hj,
        ZMod.natCast_zmod_val, ZMod.natCast_self]
      field_simp
      ring
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [pow_add, pow_mul, hy, hz]
    linear_combination hc + (l : ℤ_[l]) ^ (k + 1) * hd

theorem exists_lift {l : ℕ} [hl : Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (hΔ : Nat.card Δ = l - 1) (x : (ZMod l)ˣ) :
    ∃ δ ∈ Δ, PadicInt.toZMod (δ : ℤ_[l]) = x := by
  let f : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →* ZMod l)).comp Δ.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have h1 : PadicInt.toZMod ((δ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := congrArg Units.val hδ
    have h2 : ((δ : ℤ_[l]ˣ) : ℤ_[l]) ^ (l - 1) = 1 := by
      have : δ ^ (l - 1) = 1 := by rw [← hΔ]; exact pow_card_eq_one'
      have := congrArg (fun t : Δ => ((t : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa using this
    have h3 := geom_sum_mul ((δ : ℤ_[l]ˣ) : ℤ_[l]) (l - 1)
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · exfalso
      have := congrArg (PadicInt.toZMod (p := l)) h
      simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, map_zero] at this
      rw [Nat.cast_pred hl.out.pos] at this
      simp at this
    · ext
      simpa using sub_eq_zero.1 h
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hΔ, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨δ, hδ⟩ := hbij.2 x
  exact ⟨δ, δ.2, congrArg Units.val hδ⟩

theorem exists_root_mul_pow_approx :
    ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (u : ℤ_[l]), l ≠ 2 →
      Nat.card Δ = l - 1 → Associated (u - 1) (l : ℤ_[l]) → ∀ k a : ℕ, ¬ l ∣ a →
      ∃ δ ∈ Δ, ∃ m : ℕ, (l : ℤ_[l]) ^ k ∣ (a : ℤ_[l]) - (δ : ℤ_[l]) * u ^ m := by
  intro l hl Δ _ u h2 hΔ hu k a ha
  have ha0 : (a : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨δ, hδ, hδa⟩ := exists_lift Δ hΔ (Units.mk0 _ ha0)
  have hx : (l : ℤ_[l]) ∣ (a : ℤ_[l]) * (δ⁻¹ : ℤ_[l]ˣ) - 1 := by
    have : (l : ℤ_[l]) ∣ (a : ℤ_[l]) - δ := by
      rw [dvd_iff_toZMod, map_sub, hδa]; simp
    have h := this.mul_right ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    rwa [sub_mul, Units.mul_inv] at h
  obtain ⟨m, hm⟩ := exists_pow_approx u h2 hu _ hx k
  refine ⟨δ, hδ, m, (pow_dvd_pow _ (Nat.le_succ k)).trans ?_⟩
  have h := hm.mul_left (δ : ℤ_[l])
  rwa [mul_sub, mul_comm (a : ℤ_[l]), Units.mul_inv_cancel_left] at h

end GlobalTheory.PadicUnitGen
