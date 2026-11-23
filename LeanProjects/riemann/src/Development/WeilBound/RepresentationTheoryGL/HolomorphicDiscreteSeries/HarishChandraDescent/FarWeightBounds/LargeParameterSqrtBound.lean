import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Restrict

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

namespace FarParameters

theorem large_parameter_sqrt_bound {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : (A + B + 1) ^ 2 ≤ t) :
    A + B * Real.sqrt t < t ∧ 1 ≤ Real.sqrt t := by
  have ht0 : 0 ≤ t := le_trans (sq_nonneg _) ht
  have hs : A + B + 1 ≤ Real.sqrt t := by
    have h2 := Real.sqrt_le_sqrt ht
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have hs1 : 1 ≤ Real.sqrt t := by linarith
  refine ⟨?_, hs1⟩
  have h3 : Real.sqrt t * (A + B + 1) ≤ Real.sqrt t * Real.sqrt t :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  have h4 : 0 ≤ (Real.sqrt t - 1) * A := mul_nonneg (by linarith) hA
  nlinarith

theorem umem {n : ℕ} {ε : Fin n → Bool} (h : Formalism.REAL.UJ ε) : um h ∈ UJset ε :=
  h.2

end FarParameters

theorem far_of_trial_bound : Trial → Core → Far := by
  intro hT hC n ε ε' e lam d d' g hfit hover hd'
  obtain ⟨C0, hC0, hT'⟩ := hT n ε ε' e lam d d' g hfit hover
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = Real.sqrt (2 * C0) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := hk ▸ Real.sqrt_nonneg _
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈C0⌉₊ + 1 := ⟨_, rfl⟩
  have hJC : C0 + 1 ≤ (J : ℝ) := by
    rw [hJ]
    push_cast
    linarith [Nat.le_ceil C0]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((n : ℝ) ^ 3 + 4 * n + 2 + 2 * J) + (4 * (J : ℝ) ^ 2 + 2 * J * n + 2 * J) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * k + 4 * J * k := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨k + J + n, (A + B + 1) ^ 2, ?_⟩
  intro t ht hHC hgap H _ _ _ π hDS
  obtain ⟨hbig, hs1⟩ := FarParameters.large_parameter_sqrt_bound hA0 hB0 ht
  have ht0 : 0 ≤ t := le_trans (sq_nonneg _) ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have ht1 : 1 ≤ t := by nlinarith
  obtain ⟨hU, hDense, x, hx0, hxK, hxq⟩ := hT' t ht1 hHC hgap H π hDS
  have hS0 : 0 < C0 * t := by positivity
  have hsqrt : Real.sqrt (2 * (C0 * t)) = k * Real.sqrt t := by
    rw [hk, ← mul_assoc, Real.sqrt_mul (by positivity) t]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt t := ⟨_, rfl⟩
  rw [← hs] at hbig hs1 hsqrt hsq
  have hks : 0 ≤ k * s := mul_nonneg hk0 (by linarith)
  have hJks : 0 ≤ (J : ℝ) * (k * s) := mul_nonneg hJ0 hks
  have hbig' : A + B * s = ((n : ℝ) ^ 3 + 4 * n + 2 + 2 * J) + 2 * (k * s) +
      ((4 * (J : ℝ) ^ 2 + 2 * J * n + 2 * J) + 4 * (J * (k * s))) := by
    rw [hA, hB]
    ring
  have hP1 : 0 ≤ (n : ℝ) ^ 3 + 4 * n + 2 + 2 * J := by positivity
  have hP2 : 0 ≤ 4 * (J : ℝ) ^ 2 + 2 * J * n + 2 * J := by positivity
  have hcond1 : 2 * (C0 * t) <
      (J : ℝ) * (2 * (t - 2 * (Real.sqrt (2 * (C0 * t)) + J)) - 2 * n - 2) := by
    rw [hsqrt]
    have h1 : (4 * (J : ℝ) ^ 2 + 2 * J * n + 2 * J) + 4 * (J * (k * s)) < t := by linarith
    have h2 : (J : ℝ) * (2 * (t - 2 * (k * s + J)) - 2 * n - 2) =
        2 * J * t - ((4 * (J : ℝ) ^ 2 + 2 * J * n + 2 * J) + 4 * (J * (k * s))) := by ring
    rw [h2]
    have h3 : (2 * C0 + 1) * t ≤ 2 * J * t := by
      apply mul_le_mul_of_nonneg_right _ ht0
      linarith
    nlinarith
  have hcond2 : (n : ℝ) ^ 3 + 4 * n + 2 + 2 * (Real.sqrt (2 * (C0 * t)) + J) ≤ t := by
    rw [hsqrt]
    linarith
  have hτ : ∀ a b : Fin n, a < b → t ≤ (t • d') a - (t • d') b := by
    intro a b hab
    simp only [Pi.smul_apply, smul_eq_mul]
    have := mul_le_mul_of_nonneg_left (hd' a b hab) ht0
    linarith [mul_sub t (d' a) (d' b)]
  obtain ⟨mu, hmu, hbd, hmap⟩ := hC n ε' H (res e π) hU hDense (t • d') (C0 * t) t J x hS0 hx0 hxK
    (by simpa [mul_assoc] using hxq) hτ hcond1 hcond2
  refine ⟨mu, hmu, ?_, ?_⟩
  · intro a
    have h1 := hbd a
    rw [hsqrt] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [← hs]
    have h2 : (J : ℝ) ≤ J * s := by
      have := mul_le_mul_of_nonneg_left hs1 hJ0
      linarith
    have h3 : (n : ℝ) ≤ n * s := by
      have := mul_le_mul_of_nonneg_left hs1 hn0
      linarith
    have h4 : (k + J + n) * s = k * s + J * s + n * s := by ring
    rw [h4]
    linarith
  · intro H' _ _ _ σ hσ
    obtain ⟨j, hj0, hj⟩ := hmap H' σ hσ
    refine ⟨j, hj0, ?_⟩
    intro h y
    exact hj (um h) (FarParameters.umem h) y

end PositivityTheory.RgHe3
