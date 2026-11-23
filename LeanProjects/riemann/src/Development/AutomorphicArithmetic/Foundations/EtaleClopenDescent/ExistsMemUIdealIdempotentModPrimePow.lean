import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

private theorem UpperTheory.Cb.idempotent_lift_succ_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R) (k : ℕ)
    (a : R) (ha : a ∈ I) (h1 : P ^ (k + 1) ∣ a + σ a - 1) (h2 : P ^ (k + 1) ∣ a * σ a) :
    ∃ a' ∈ I, P ^ (k + 2) ∣ a' + σ a' - 1 ∧ P ^ (k + 2) ∣ a' * σ a' := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  refine ⟨3 * a ^ 2 - 2 * a ^ 3, ?_, ?_, ?_⟩
  · have h3 : a ^ 2 * (3 - 2 * a) ∈ I := I.mul_mem_right _ (by
      rw [pow_two]
      exact I.mul_mem_left _ ha)
    have e : 3 * a ^ 2 - 2 * a ^ 3 = a ^ 2 * (3 - 2 * a) := by ring
    rw [e]
    exact h3
  · have e1 : 3 * a ^ 2 - 2 * a ^ 3 + σ (3 * a ^ 2 - 2 * a ^ 3) - 1 =
        -3 * (a + σ a - 1) ^ 2 - 2 * (a + σ a - 1) ^ 3 + 6 * (a * σ a) * (a + σ a - 1) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e1, hc, hd]
    exact ⟨P ^ k * (-3 * c ^ 2 - 2 * P ^ (k + 1) * c ^ 3 + 6 * d * c), by ring⟩
  · have e2 : (3 * a ^ 2 - 2 * a ^ 3) * σ (3 * a ^ 2 - 2 * a ^ 3) =
        (a * σ a) ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e2, hd]
    exact ⟨P ^ k * d ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)), by ring⟩

private theorem UpperTheory.Cb.exists_idempotent_lift_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R)
    (a : R) (ha : a ∈ I) (h1 : P ∣ a + σ a - 1) (h2 : P ∣ a * σ a) (k : ℕ) :
    ∃ a' ∈ I, P ^ (k + 1) ∣ a' + σ a' - 1 ∧ P ^ (k + 1) ∣ a' * σ a' := by
  induction k with
  | zero => exact ⟨a, ha, by simpa using h1, by simpa using h2⟩
  | succ k ih =>
    obtain ⟨b, hb, hb1, hb2⟩ := ih
    exact UpperTheory.Cb.idempotent_lift_succ_pow σ P I k b hb hb1 hb2

theorem UpperTheory.Cb.exists_mem_uIdeal_idempotent_mod_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (e : ℕ), w ≠ ⊤ → uIdeal D r ≤ w → ∃ a ∈ uIdeal D r, (p : 𝓞 D.F) ^ e ∣ a + D.bar a - 1 ∧ (p : 𝓞 D.F) ^ e ∣ a * D.bar a := by
  intro p _ D r w e hw hle
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  set x : 𝓞 D.F := D.ω - (r : 𝓞 D.F) with hx
  set N : ℤ := r ^ 2 - D.tr * r + D.nm with hN
  set s : ℤ := D.tr - 2 * r with hs
  have hbx : D.bar x = D.bar D.ω - (r : 𝓞 D.F) := by
    simp [x, map_sub, map_intCast]
  have hxN : x * D.bar x = (N : 𝓞 D.F) := by
    rw [hbx]
    push_cast [N]
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hxs : x + D.bar x = (s : 𝓞 D.F) := by
    rw [hbx]
    push_cast [s]
    linear_combination D.tr_eq
  have hpN : (p : ℤ) ∣ N := by
    by_contra hnd
    obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hnd
    apply hw
    rw [Ideal.eq_top_iff_one]
    have hpw : ((p : ℤ) : 𝓞 D.F) ∈ w := by
      have := hle (p_mem_uIdeal D r)
      simpa using this
    have hNw : ((N : ℤ) : 𝓞 D.F) ∈ w := by
      rw [← hxN]
      exact w.mul_mem_right _ (hle (sub_mem_uIdeal D r))
    have h1 : ((u * p + v * N : ℤ) : 𝓞 D.F) ∈ w := by
      push_cast
      exact w.add_mem (w.mul_mem_left _ (by simpa using hpw)) (w.mul_mem_left _ hNw)
    rw [huv] at h1
    simpa using h1
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hd
    apply D.disc_p
    have e : D.tr ^ 2 - 4 * D.nm = s ^ 2 - 4 * N := by
      simp only [s, N]
      ring
    rw [e]
    exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_mul_of_dvd_right hpN 4)
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hps
  obtain ⟨N', hN'⟩ := hpN
  have ha : (v : 𝓞 D.F) * x ∈ uIdeal D r := (uIdeal D r).mul_mem_left _ (sub_mem_uIdeal D r)
  have h1 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x + D.bar ((v : 𝓞 D.F) * x) - 1 := by
    refine ⟨-(u : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x + (v : 𝓞 D.F) * D.bar x - 1 = (v : 𝓞 D.F) * (x + D.bar x) - 1 := by ring
    rw [e, hxs]
    have huv' : ((u * p + v * s : ℤ) : 𝓞 D.F) = 1 := by rw [huv]; simp
    push_cast at huv'
    linear_combination huv'
  have h2 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x * D.bar ((v : 𝓞 D.F) * x) := by
    refine ⟨(v : 𝓞 D.F) ^ 2 * (N' : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x * ((v : 𝓞 D.F) * D.bar x) = (v : 𝓞 D.F) ^ 2 * (x * D.bar x) := by ring
    rw [e, hxN, hN']
    push_cast
    ring
  obtain ⟨a', ha', h1', h2'⟩ := UpperTheory.Cb.exists_idempotent_lift_pow (D.bar : 𝓞 D.F →+* 𝓞 D.F) (p : 𝓞 D.F)
    (uIdeal D r) _ ha (by simpa using h1) (by simpa using h2) e
  refine ⟨a', ha', ?_, ?_⟩
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h1')
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h2')
