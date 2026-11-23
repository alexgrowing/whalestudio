import Mathlib

open Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg

theorem hensel_quad (p : ℕ) [Fact p.Prime] (a b t : ℤ)
    (h : ‖((a * t ^ 2 + b : ℤ) : ℤ_[p])‖ < ‖((2 * a * t : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], (a : ℤ_[p]) * z ^ 2 + (b : ℤ_[p]) = 0 := by
  have h1 : aeval (t : ℤ_[p]) (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p])) =
      ((a * t ^ 2 + b : ℤ) : ℤ_[p]) := by
    simp
  have h2 : aeval (t : ℤ_[p]) (derivative (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))) =
      ((2 * a * t : ℤ) : ℤ_[p]) := by
    simp
    ring
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))
    (a := (t : ℤ_[p])) (by rw [h1, h2]; exact h)
  exact ⟨z, by simpa using hz⟩

theorem norm_unit (p : ℕ) [Fact p.Prime] (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : ‖(k : ℤ_[p])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  exact h ((PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := k)).1 (not_le.1 hlt))

private theorem padic_norm_lt_norm_sq_of_dvd_of_not_dvd (p : ℕ) [Fact p.Prime] (u v : ℤ) (hu : (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) : ‖(u : ℤ_[p])‖ < ‖(v : ℤ_[p])‖ ^ 2 := by
  rw [norm_unit p v hv, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := u)).2 hu

theorem rep_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hcp : (c : ZMod p) ≠ 0 := fun h => hc ((CharP.cast_eq_zero_iff (ZMod p) p c).1 h)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  obtain ⟨u, v, huv⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 + C (1 : ZMod p)) (g := C (c : ZMod p) * X ^ 2)
    (by simpa using degree_X_pow_add_C (R := ZMod p) (n := 2) (by norm_num) 1)
    (by simpa using degree_C_mul_X_pow 2 hcp) hodd
  obtain ⟨x₀, rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨y₀, rfl⟩ := ZMod.intCast_surjective v
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')
  have hcz : ¬ (p : ℤ) ∣ (c : ℤ) := by exact_mod_cast hc
  have hdiv : (p : ℤ) ∣ x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at huv
    push_cast
    linear_combination huv
  by_cases hx : (p : ℤ) ∣ x₀
  · have hy : ¬ (p : ℤ) ∣ y₀ := by
      intro hy
      have h1 : (p : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1) - (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2) := by ring
        rw [e]
        exact dvd_sub hdiv (dvd_add (dvd_pow hx two_ne_zero)
          (dvd_mul_of_dvd_right (dvd_pow hy two_ne_zero) (c : ℤ)))
      exact hpz.not_dvd_one h1
    obtain ⟨z, hz⟩ := hensel_quad p c (x₀ ^ 2 + 1) y₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim (fun h => (hpz.dvd_or_dvd h).elim h2 hcz) hy))
    exact ⟨x₀, z, by push_cast at hz; linear_combination hz⟩
  · obtain ⟨z, hz⟩ := hensel_quad p 1 (c * y₀ ^ 2 + 1) x₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim
          (fun h => (hpz.dvd_or_dvd h).elim h2 hpz.not_dvd_one) hx))
    exact ⟨z, y₀, by push_cast at hz; linear_combination hz⟩

theorem rep_two (c : ℕ) (hc : c % 8 = 3) : ∃ x y : ℤ_[2], x ^ 2 + (c : ℤ_[2]) * y ^ 2 = -1 := by
  have h8 : ((2 : ℕ) : ℤ) ^ 3 ∣ (c : ℤ) * 1 ^ 2 + 5 := by
    norm_num; omega
  have hc2 : ¬ ((2 : ℕ) : ℤ) ∣ (c : ℤ) := by
    push_cast; omega
  have hB : ‖((2 * (c : ℤ) * 1 : ℤ) : ℤ_[2])‖ = 2⁻¹ := by
    rw [show (2 * (c : ℤ) * 1 : ℤ) = ((2 : ℕ) : ℤ) * c by push_cast; ring, Int.cast_mul, norm_mul,
      norm_unit 2 c hc2, Int.cast_natCast, PadicInt.norm_p]
    norm_num
  obtain ⟨z, hz⟩ := hensel_quad 2 c 5 1 (by
    rw [hB]
    refine lt_of_le_of_lt ((PadicInt.norm_int_le_pow_iff_dvd (p := 2)
      (k := (c : ℤ) * 1 ^ 2 + 5) (n := 3)).2 h8) ?_
    norm_num [zpow_neg])
  exact ⟨2, z, by push_cast at hz; linear_combination hz⟩

def Rep (q d m : ℕ) : Prop :=
  ∃ α β γ δ : ZMod m, (α ^ 2 + (q : ZMod m) * β ^ 2) * (γ ^ 2 + (d : ZMod m) * δ ^ 2) = -1

theorem rep_pp (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (p k : ℕ) (hp : p.Prime) :
    Rep q d (p ^ k) := by
  have := Fact.mk hp
  have key : ∀ c : ℕ, (∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1) →
      ∃ α β : ZMod (p ^ k), α ^ 2 + (c : ZMod (p ^ k)) * β ^ 2 = -1 := by
    rintro c ⟨x, y, h⟩
    refine ⟨PadicInt.toZModPow k x, PadicInt.toZModPow k y, ?_⟩
    simpa using congrArg (PadicInt.toZModPow (p := p) k) h
  rcases eq_or_ne p q with hpq | hpq
  · have hp2 : p ≠ 2 := by
      rintro rfl; rw [← hpq] at hq8; norm_num at hq8
    have hpd : ¬ p ∣ d := fun h =>
      hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 (by rwa [← hpq]))
    obtain ⟨γ, δ, h⟩ := key d (rep_odd p hp2 d hpd)
    exact ⟨1, 0, γ, δ, by simp [h]⟩
  · rcases eq_or_ne p 2 with hp2 | hp2
    · subst hp2
      obtain ⟨α, β, h⟩ := key q (rep_two q hq8)
      exact ⟨α, β, 1, 0, by simp [h]⟩
    · have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
      obtain ⟨α, β, h⟩ := key q (rep_odd p hp2 q hpq')
      exact ⟨α, β, 1, 0, by simp [h]⟩

private theorem rep_mul_of_coprime {q d a b : ℕ} (hab : Nat.Coprime a b)
    (ha : Rep q d a) (hb : Rep q d b) :
    Rep q d (a * b) := by
  obtain ⟨α₁, β₁, γ₁, δ₁, h₁⟩ := ha
  obtain ⟨α₂, β₂, γ₂, δ₂, h₂⟩ := hb
  let e := ZMod.chineseRemainder hab
  refine ⟨e.symm (α₁, α₂), e.symm (β₁, β₂), e.symm (γ₁, γ₂), e.symm (δ₁, δ₂), e.injective ?_⟩
  simp only [map_mul, map_add, map_pow, map_natCast, map_neg, map_one,
    RingEquiv.apply_symm_apply]
  ext <;> simp [h₁, h₂]

theorem rep_all (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) :
    0 < m → Rep q d m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact fun _ => rep_pp q d hq hd hq8 hqd p n hp
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | one =>
    intro _
    simpa using rep_pp q d hq hd hq8 hqd 2 0 Nat.prime_two
  | coprime a b ha1 hb1 hab ha hb =>
    exact fun _ => rep_mul_of_coprime hab (ha (by omega)) (hb (by omega))

theorem rep_int (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) (hm : 0 < m) :
    ∃ α β γ δ s : ℤ, (α ^ 2 + q * β ^ 2) * (γ ^ 2 + d * δ ^ 2) = -1 + m * s := by
  obtain ⟨α, β, γ, δ, h⟩ := rep_all q d hq hd hq8 hqd m hm
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective α
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective β
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective γ
  obtain ⟨e, rfl⟩ := ZMod.intCast_surjective δ
  have hdvd : (m : ℤ) ∣ (a ^ 2 + q * b ^ 2) * (c ^ 2 + d * e ^ 2) + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod m) m]
    push_cast
    linear_combination h
  obtain ⟨s, hs⟩ := hdvd
  exact ⟨a, b, c, e, s, by linear_combination hs⟩

end Formalism.L2.PairingIndexBounds.Eq.J.Neg
