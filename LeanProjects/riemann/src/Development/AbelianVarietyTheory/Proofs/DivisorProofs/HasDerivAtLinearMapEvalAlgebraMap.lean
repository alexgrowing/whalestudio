import Mathlib

open Filter Topology

namespace GlobalTheory

open Polynomial in

theorem hasDerivAt_linearMap_eval_algebraMap {A : Type*} [CommRing A] [Algebra ℝ A]
    (Φ : A →ₗ[ℝ] ℝ) (R : Polynomial A) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Φ (R.eval (algebraMap ℝ A t)))
      (Φ ((derivative R).eval (algebraMap ℝ A τ))) τ := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, derivative_add]
    exact hp.add hq
  | monomial n a =>
    simp only [eval_monomial, derivative_monomial]
    have h1 : ∀ (m : ℕ) (t : ℝ), Φ (a * (algebraMap ℝ A t) ^ m) = t ^ m * Φ a := by
      intro m t
      rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    have h2 : Φ (a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1)) = (n : ℝ) * τ ^ (n - 1) * Φ a := by
      have : a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1) = n • (a * (algebraMap ℝ A τ) ^ (n - 1)) := by
        rw [nsmul_eq_mul]; ring
      rw [this, map_nsmul, h1, nsmul_eq_mul]; ring
    have h3 : (fun t : ℝ => Φ (a * (algebraMap ℝ A t) ^ n)) = fun t => t ^ n * Φ a := funext (h1 n)
    rw [h3, h2]
    exact (hasDerivAt_pow n τ).mul_const (Φ a)

theorem monotone_form_along_segment : ∀ (D : ℕ) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ),
    (∀ x y : ℕ, 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) *
      (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D)) →
    Φ (MvPolynomial.X 1 ^ (D + 1)) ≤ Φ (MvPolynomial.X 0 ^ (D + 1)) := by
  intro D Φ hyp
  have hΦC : ∀ (r : ℝ) (q : MvPolynomial (Fin 2) ℝ), Φ (MvPolynomial.C r * q) = r * Φ q := by
    intro r q; rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
  set a : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 with ha
  set b : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 - MvPolynomial.X 1 with hb
  set Q : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ (D + 1) with hQ
  set R : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    Polynomial.C b * (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ D with hR
  set g : ℝ → ℝ := fun t => Φ (Q.eval (algebraMap ℝ _ t)) with hg
  set f : ℝ → ℝ := fun t => Φ (R.eval (algebraMap ℝ _ t)) with hf
  have hgd : ∀ τ, HasDerivAt g (((D : ℝ) + 1) * f τ) τ := by
    intro τ
    convert hasDerivAt_linearMap_eval_algebraMap Φ Q τ using 1
    simp [hf, hQ, hR, Polynomial.derivative_pow]
    have hc : ((D : MvPolynomial (Fin 2) ℝ) + 1) = MvPolynomial.C ((D : ℝ) + 1) := by simp
    rw [hc, mul_assoc, hΦC]
    congr 2
    ring
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact (hasDerivAt_linearMap_eval_algebraMap Φ R τ).continuousAt
  have hfrat : ∀ x n : ℕ, 0 < n → x ≤ n → 0 ≤ f ((x : ℝ) / n) := by
    intro x n hn hxn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : a + MvPolynomial.C ((x : ℝ) / n) * b = MvPolynomial.C (1 / (n : ℝ)) *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) := by
      rw [Nat.cast_sub hxn]
      have h1 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C (x : ℝ) =
          (MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul]; congr 1; ring
      have h2 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C ((n : ℝ) - x) =
          (1 - MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul, ← map_one MvPolynomial.C, ← map_sub]; congr 1; field_simp
      rw [ha, hb]
      linear_combination (-(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ)) * h1 - (MvPolynomial.X 1) * h2
    have hfx : f ((x : ℝ) / n) = (1 / (n : ℝ)) ^ D * Φ (b *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) ^ D) := by
      simp only [hf, hR, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, MvPolynomial.algebraMap_eq]
      rw [e, mul_pow, ← map_pow, mul_left_comm, hΦC]
    rw [hfx]
    exact mul_nonneg (pow_nonneg (by positivity) _) (hyp _ _)
  have hfpos : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f τ := by
    intro τ hτ
    by_contra hneg
    push_neg at hneg
    have hev : ∀ᶠ t in 𝓝 τ, f t < 0 := hfc.continuousAt.eventually (Iio_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (τ - ε) < τ from
      max_lt hτ.1 (by linarith))
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
    have hqε : τ - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have hnum : 0 < q.num := Rat.num_pos.mpr hq0'
    have hx : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have hqdef : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [hx]; exact_mod_cast (Rat.num_div_den q).symm
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hle : q.num.toNat ≤ q.den := by
      have h1 : (q : ℝ) < 1 := by linarith [hτ.2]
      rw [hqdef, div_lt_one hden] at h1
      exact_mod_cast h1.le
    have h0 := hfrat q.num.toNat q.den q.den_pos hle
    rw [← hqdef] at h0
    have hd : dist (q : ℝ) τ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball hd]
  have hgdiff : ∀ τ, DifferentiableAt ℝ g τ := fun τ => (hgd τ).differentiableAt
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun τ _ => (hgdiff τ).continuousAt.continuousWithinAt
    · exact fun τ _ => (hgdiff τ).differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [(hgd τ).deriv]
      exact mul_nonneg (by positivity) (hfpos τ hτ)
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simpa [hg, hQ, ha, hb] using h01

end GlobalTheory
