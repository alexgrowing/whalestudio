import Mathlib
open Complex Filter Topology

namespace GlobalTheory

theorem rankin_convolution_coeff_of_squareSupported (e : ℕ) (χ ψ θ g b z : ℕ → ℂ)
    (hψ : ∀ m n, ψ (m * n) = ψ m * ψ n) (hθ : ∀ m n, θ (m * n) = θ m * θ n)
    (hg : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2))
    (hb : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2)
    (hz : ∀ a, z a = if Nat.sqrt a * Nat.sqrt a = a then χ (Nat.sqrt a) * ψ (Nat.sqrt a) * θ (Nat.sqrt a) * (Nat.sqrt a : ℂ) ^ (3 * e - 1) else 0)
    (n : ℕ) (hn : n ≠ 0) :
    LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n
      = LSeries.convolution z (fun n : ℕ => g n * b n) n := by
  simp only [LSeries.convolution_def]
  have hL : ∀ p ∈ n.divisorsAntidiagonal, (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2)
      = ∑ δ ∈ (Nat.gcd p.1 p.2).divisors, χ δ * (δ:ℂ)^(2*e) * ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * g (n / δ^2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h1 : 0 < p.1 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, zero_mul]))
    have h2 : 0 < p.2 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, mul_zero]))
    rw [show (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2) = ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * (g p.1 * g p.2) by ring, hg _ _ h1 h2, Finset.mul_sum, hp.1]
    exact Finset.sum_congr rfl (fun δ _ => by ring)
  have hR : ∀ p ∈ n.divisorsAntidiagonal, z p.1 * (g p.2 * b p.2)
      = ∑ q ∈ p.2.divisorsAntidiagonal, z p.1 * g p.2 * (ψ q.1 * (q.1:ℂ)^(e-1) * θ q.2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := fun h => hn (by rw [← hp.1, h, mul_zero])
    rw [hb _ h2, ← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_sigma', Finset.sum_sigma']
  have key : ∀ s x y : ℕ, 0 < s → s * s * (x * y) = n →
      z (s * s) * g (x * y) * (ψ x * (x:ℂ)^(e-1) * θ y)
        = χ s * (s:ℂ)^(2*e) * ψ (s * x) * ((s * x : ℕ):ℂ)^(e-1) * θ (s * y) * g (n / s^2) := by
    intro s x y hs hn'
    have hsq : Nat.sqrt (s * s) = s := Nat.sqrt_eq s
    have hdiv : n / s^2 = x * y := by
      rw [← hn', sq, Nat.mul_div_cancel_left _ (Nat.mul_pos hs hs)]
    have hpow : (s:ℂ)^(2*e) * (s:ℂ)^(e-1) = (s:ℂ)^(3*e-1) := by
      rw [← pow_add]; congr 1; omega
    rw [hz, hsq, if_pos rfl, hdiv, hψ, hθ, ← hpow]
    push_cast
    rw [mul_pow]
    ring
  have dec : ∀ a : (_ : ℕ × ℕ) × (ℕ × ℕ), a ∈ n.divisorsAntidiagonal.sigma (fun p => p.2.divisorsAntidiagonal) →
      z a.1.1 * g a.1.2 * (ψ a.2.1 * (a.2.1:ℂ)^(e-1) * θ a.2.2) ≠ 0 →
      ∃ s x y : ℕ, 0 < s ∧ s * s * (x * y) = n ∧ a = ⟨(s * s, x * y), (x, y)⟩ := by
    rintro ⟨⟨a, c⟩, ⟨x, y⟩⟩ hmem hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hmem
    obtain ⟨⟨hac, -⟩, hxy, -⟩ := hmem
    have h : Nat.sqrt a * Nat.sqrt a = a := by
      by_contra h
      apply hne
      simp only [hz, if_neg h, zero_mul]
    have ha : a ≠ 0 := fun h0 => hn (by rw [← hac, h0, zero_mul])
    refine ⟨Nat.sqrt a, x, y, Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero ha), by rw [h, hxy, hac], ?_⟩
    rw [h, hxy]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => (⟨(Nat.sqrt a.1.1 * a.2.1, Nat.sqrt a.1.1 * a.2.2), Nat.sqrt a.1.1⟩ : (_ : ℕ × ℕ) × ℕ)) ?_ ?_ ?_ ?_
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; apply hn; rw [← hn']; ring)
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors, Nat.sqrt_eq]
    refine ⟨⟨by rw [← hn']; ring, hn⟩, Nat.dvd_gcd (dvd_mul_right s x) (dvd_mul_right s y),
      (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hs hx)).ne'⟩
  · intro a1 h11 h12 a2 h21 h22 heq
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a1 h11 h12
    obtain ⟨t, u, v, ht, hn'', rfl⟩ := dec a2 h21 h22
    simp only [Nat.sqrt_eq, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at heq
    obtain ⟨⟨h1, h2⟩, h3⟩ := heq
    subst h3
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h1
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h2
    rfl
  · rintro ⟨⟨x, y⟩, δ⟩ hb0 hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors] at hb0
    obtain ⟨⟨hxy, -⟩, hδ, hg0⟩ := hb0
    have hδ0 : 0 < δ := Nat.pos_of_dvd_of_pos hδ (Nat.pos_of_ne_zero hg0)
    obtain ⟨x', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_left x y)
    obtain ⟨y', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_right (δ * x') y)
    have hn'' : δ * δ * (x' * y') = n := by rw [← hxy]; ring
    have hxy0 : x' * y' ≠ 0 := fun h0 => hn (by rw [← hn'', h0, mul_zero])
    refine ⟨⟨(δ * δ, x' * y'), (x', y')⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hn'', hn⟩, trivial, hxy0⟩
    · intro h0
      apply hne
      refine Eq.trans ?_ h0
      exact (key δ x' y' hδ0 hn'').symm
    · simp only [Nat.sqrt_eq]
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    simp only [Nat.sqrt_eq]
    exact key s x y hs hn'

theorem rankin_convolution_coeff : ∀ (e : ℕ) (χ ψ θ g b : ℕ → ℂ), (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → ∀ n : ℕ, n ≠ 0 → LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n = LSeries.convolution (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (fun n : ℕ => g n * b n) n := by
  intro e χ ψ θ g b hψ hθ hg hb n hn
  exact rankin_convolution_coeff_of_squareSupported e χ ψ θ g b _ hψ hθ hg hb (fun _ => rfl) n hn

end GlobalTheory
