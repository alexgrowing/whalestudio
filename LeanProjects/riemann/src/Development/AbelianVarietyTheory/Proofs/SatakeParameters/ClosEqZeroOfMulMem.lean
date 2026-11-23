import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta

open GlobalTheory.Pst.StLat

namespace GlobalTheory.Pst.StLat

theorem clos_eq_zero_of_mul_mem {R : Type} [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hpu : IsUnit ((p : ℕ) : R)) (π : R) (hπ : π ≠ 0)
    (hsep : ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (S : Subring R)
    (hdiv : ∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s')
    (hres : ∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y)
    (u : R) (hlog : ∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
      π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m))
    (a : R) (r : ℕ) (ha : a ∈ Clos S π) (hau : ((p : ℕ) : R) ^ r * a * u ∈ Clos S π) : a = 0 := by
  obtain ⟨q, hPq⟩ : ∃ q : R, ((p : ℕ) : R) * q = 1 := ⟨((hpu.unit⁻¹ : Rˣ) : R), hpu.mul_val_inv⟩
  have hSC : ∀ s ∈ S, s ∈ Clos S π := fun s hs n => ⟨s, hs, by simp⟩
  have hPC : ((p : ℕ) : R) ∈ Clos S π := natCast_mem _ _

  have stepD : ∀ b ∈ Clos S π, ∀ r' : ℕ, ((p : ℕ) : R) ^ r' * b * u ∈ Clos S π →
      ∃ b' ∈ Clos S π, ((p : ℕ) : R) * b' = b := by
    intro b hb r' hbu
    refine ⟨q * b, ?_, by rw [← mul_assoc, hPq, one_mul]⟩
    intro n
    obtain ⟨s, hs, e, he, w, hw⟩ := hlog (r' + n + 1) (by omega)
    have hm : r' + n + 1 - 1 = r' + n := by omega
    rw [hm] at hw
    set M := p ^ (r' + n + 1) with hMdef
    have hnM : n ≤ M := by
      have h1 : r' + n + 1 < p ^ (r' + n + 1) := Nat.lt_pow_self hp.one_lt
      omega
    have h2M : π ^ (2 * M) = π ^ M * π ^ M := by rw [two_mul, pow_add]
    rw [h2M] at hw
    have hx : b * (((p : ℕ) : R) ^ (r' + n) * u - s) ∈ Clos S π := by
      have : b * (((p : ℕ) : R) ^ (r' + n) * u - s) =
          ((p : ℕ) : R) ^ n * (((p : ℕ) : R) ^ r' * b * u) - b * s := by ring
      rw [this]
      exact sub_mem (mul_mem (pow_mem hPC _) hbu) (mul_mem hb (hSC s hs))
    obtain ⟨s₁, hs₁, c, hc⟩ := hx (2 * M)
    rw [h2M] at hc
    have hs1eq : s₁ = π ^ M * (q * b * e + π ^ M * (q * b * w - c)) := by
      linear_combination (-1 : R) * hc + (q * b) * hw - (b * (((p : ℕ) : R) ^ (r' + n) * u - s)) * hPq
    obtain ⟨s₂, hs₂S, hs₂⟩ := hdiv s₁ hs₁ M ⟨_, hs1eq⟩
    have hcan : q * b * e - s₂ = π ^ M * (c - q * b * w) := by
      apply mul_left_cancel₀ (pow_ne_zero M hπ)
      linear_combination hs₂ - hs1eq
    have he2 : e * e = 1 := by rcases he with rfl | rfl <;> ring
    have heS : e * s₂ ∈ S := by
      rcases he with rfl | rfl
      · simpa using hs₂S
      · simpa using neg_mem hs₂S
    refine ⟨e * s₂, heS, dvd_trans (pow_dvd_pow π hnM) ⟨e * (c - q * b * w), ?_⟩⟩
    linear_combination e * hcan - (q * b) * he2

  have iter : ∀ k : ℕ, ∃ b ∈ Clos S π, ((p : ℕ) : R) ^ k * b = a ∧
      ((p : ℕ) : R) ^ (r + k) * b * u ∈ Clos S π := by
    intro k
    induction k with
    | zero => exact ⟨a, ha, by simp, by simpa using hau⟩
    | succ k ih =>
      obtain ⟨b, hb, hbk, hbu⟩ := ih
      obtain ⟨b', hb', hPb'⟩ := stepD b hb (r + k) hbu
      refine ⟨b', hb', ?_, ?_⟩
      · rw [pow_succ, mul_assoc, hPb', hbk]
      · have : ((p : ℕ) : R) ^ (r + (k + 1)) * b' * u =
            ((p : ℕ) : R) ^ (r + k) * (((p : ℕ) : R) * b') * u := by ring
        rw [this, hPb']
        exact hbu

  by_contra ha0
  classical
  have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
    by_contra h
    push_neg at h
    exact ha0 (hsep a h)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd a)
  set i := Nat.find hex - 1 with hidef
  have hi1 : i + 1 = Nat.find hex := by omega
  have hia : π ^ i ∣ a := by
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    simpa using this
  obtain ⟨a₁, ha₁⟩ := hia
  have hna₁ : ¬ π ∣ a₁ := by
    rintro ⟨t, ht⟩
    apply Nat.find_spec hex
    rw [← hi1]
    exact ⟨t, by rw [ha₁, ht, pow_succ]; ring⟩
  apply hna₁
  apply hres a₁
  intro k
  obtain ⟨b, hb, hbk, -⟩ := iter k
  obtain ⟨s, hs, hbs⟩ := hb (i + 1)
  have hib : π ^ i ∣ b := ⟨q ^ k * a₁, by
    have : b = q ^ k * (((p : ℕ) : R) ^ k * b) := by
      rw [← mul_assoc, ← mul_pow, mul_comm q, hPq, one_pow, one_mul]
    rw [this, hbk, ha₁]; ring⟩
  have his : π ^ i ∣ s := by
    have h1 : π ^ i ∣ b - s := dvd_trans (pow_dvd_pow π (Nat.le_succ i)) hbs
    have := dvd_sub hib h1
    simpa using this
  obtain ⟨s', hs'S, hs'⟩ := hdiv s hs i his
  refine ⟨s', hs'S, ?_⟩
  rw [← mul_dvd_mul_iff_left (pow_ne_zero i hπ), ← pow_succ]
  have : π ^ i * (a₁ - ((p : ℕ) : R) ^ k * s') = ((p : ℕ) : R) ^ k * (b - s) := by
    rw [mul_sub, ← ha₁, ← hbk, hs']; ring
  rw [this]
  exact dvd_mul_of_dvd_right hbs _

end GlobalTheory.Pst.StLat
