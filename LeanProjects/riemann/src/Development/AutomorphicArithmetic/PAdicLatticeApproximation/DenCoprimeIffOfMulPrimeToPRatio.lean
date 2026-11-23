import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma den_coprime_of_mul_eq (p : ℕ) (u v : ℚ) (a b : ℕ) (hb : 0 < b) (hbp : b.Coprime p)
    (h : u * a = v * b) (hu : u.den.Coprime p) : v.den.Coprime p := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hv : v = u * Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    field_simp
    linarith [h]
  have h1 : (Rat.divInt (a : ℤ) (b : ℤ)).den ∣ b := by exact_mod_cast Rat.den_dvd a b
  have h2 := Rat.mul_den_dvd u (Rat.divInt (a : ℤ) (b : ℤ))
  rw [← hv] at h2
  exact Nat.Coprime.coprime_dvd_left (h2.trans (Nat.mul_dvd_mul_left _ h1)) (Nat.Coprime.mul hu hbp)

theorem UpperTheory.den_coprime_iff_of_mul_prime_to_p_ratio :
    ∀ (p : ℕ) [Fact p.Prime] (s s₁ : ℚ) (a b : ℕ), 0 < a → 0 < b → a.Coprime p → b.Coprime p → s₁ * a = s * b → ∀ y : ℚ, (s₁ * y).den.Coprime p ↔ (s * y).den.Coprime p := by
  intro p _ s s₁ a b ha hb hap hbp h y
  constructor
  · intro hu
    exact den_coprime_of_mul_eq p (s₁ * y) (s * y) a b hb hbp (by rw [mul_right_comm, h, mul_right_comm]) hu
  · intro hu
    exact den_coprime_of_mul_eq p (s * y) (s₁ * y) b a ha hap (by rw [mul_right_comm, ← h, mul_right_comm]) hu
