import Mathlib

open scoped LSeries.notation ArithmeticFunction.Moebius
open LSeries

namespace GlobalTheory.CompanionTheory.SquareEuler

lemma natCast_pow_cpow (p e : ℕ) (s : ℂ) :
    (((p ^ e : ℕ) : ℂ)) ^ s = ((p : ℂ) ^ s) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {M : ℕ} (c : DirichletCharacter ℂ M) {N : ℕ → ℂ} {s : ℂ}

lemma term_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    LSeries.term (↗c * N) s (p ^ e) = N (p ^ e) * (c p * (p : ℂ) ^ (-s)) ^ e := by
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne, natCast_pow_cpow, Complex.cpow_neg]
  simp only [Pi.mul_apply, Nat.cast_pow, map_pow, mul_pow, inv_pow]
  rw [div_eq_mul_inv]
  ring

lemma norm_X_lt_one (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖c p * (p : ℂ) ^ (-s)‖ < 1 := by
  have h1 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa using hs)
  calc ‖c p * (p : ℂ) ^ (-s)‖ = ‖c p‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr; exact c.norm_le_one _
    _ < 1 := by simpa using h1

lemma term_mul (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    {m n : ℕ} (h : m.Coprime n) :
    LSeries.term (↗c * N) s (m * n) =
      LSeries.term (↗c * N) s m * LSeries.term (↗c * N) s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  simp only [Pi.mul_apply, hNmul h, Nat.cast_mul, map_mul]
  rw [div_mul_div_comm]
  ring_nf

lemma hasProd_twist (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hsum : LSeriesSummable N s) :
    HasProd (fun p : Nat.Primes => ∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j)
      (L (↗c * N) s) := by
  have hT : LSeriesSummable (↗c * N) s := DirichletCharacter.LSeriesSummable_mul c hsum
  have := EulerProduct.eulerProduct_hasProd (f := LSeries.term (↗c * N) s) ?_ ?_ hT.norm ?_
  · have h2 : L (↗c * N) s = ∑' n, LSeries.term (↗c * N) s n := rfl
    rw [h2]
    convert this using 2 with p
    exact tsum_congr fun j => (term_prime_pow c p.prop j).symm
  · simp [LSeries.term_of_ne_zero, hN1]
  · intro m n hmn
    exact term_mul c hNmul hmn
  · simp

lemma LSeries_twist_moebius_conv (hs : 1 < s.re) (hsum : LSeriesSummable N s) :
    L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s = (L ↗c s)⁻¹ * L (↗c * N) s := by
  have hμ : LSeriesSummable (↗c * (↗μ : ℕ → ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul c (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hT : LSeriesSummable (↗c * N) s := DirichletCharacter.LSeriesSummable_mul c hsum
  rw [← DirichletCharacter.mul_convolution_distrib, LSeries_convolution' hμ hT]
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one c hs
  rw [eq_inv_of_mul_eq_one_right h1]

lemma local_factor {A X : ℂ} (hX : ‖X‖ < 1) :
    A * (1 - X) * (1 - X ^ 2)⁻¹ = A / (1 + X) := by
  have h1 : 1 - X ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have h2 : 1 + X ≠ 0 := by
    intro h
    have : X = -1 := by linear_combination h
    simp [this] at hX
  have h3 : 1 - X ^ 2 = (1 - X) * (1 + X) := by ring
  rw [h3]
  field_simp

theorem hasProd_moebius_conv (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hs : 1 < s.re) (hsum : LSeriesSummable N s) :
    HasProd (fun p : Nat.Primes =>
        (∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
          (1 + c p * ((p : ℕ) : ℂ) ^ (-s)))
      (L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s * L ↗(c ^ 2) (2 * s)) := by
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hA := hasProd_twist c hN1 hNmul hsum
  have hB := DirichletCharacter.LSeries_eulerProduct_hasProd (c ^ 2) h2s
  have hC := DirichletCharacter.LSeries_eulerProduct_hasProd c hs
  have hCne : L ↗c s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re c hs
  have hCi := hC.inv₀ hCne
  have hP := (hA.mul hCi).mul hB
  rw [LSeries_twist_moebius_conv c hs hsum]
  convert hP using 1
  · funext p
    have hX := norm_X_lt_one c (s := s) (by linarith) p.prop
    rw [← local_factor hX, inv_inv]
    have hsq : (c ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s)) =
        (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      have h3 : -(2 * s) = ((2 : ℕ) : ℂ) * (-s) := by push_cast; ring
      rw [h3, Complex.cpow_nat_mul, mul_pow]
      congr 1
      exact MulChar.pow_apply' c (by norm_num) _
    rw [hsq]
  · ring

theorem hasProd_moebius_conv_of_norm_le (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d) (hs : 2 < s.re) :
    HasProd (fun p : Nat.Primes =>
        (∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
          (1 + c p * ((p : ℕ) : ℂ) ^ (-s)))
      (L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s * L ↗(c ^ 2) (2 * s)) := by
  refine hasProd_moebius_conv c hN1 hNmul (by linarith) ?_
  refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun n hn => ?_⟩
  have : (n : ℝ) ^ ((2 : ℝ) - 1) = n := by norm_num
  rw [this, one_mul]
  exact hNle n hn

end GlobalTheory.CompanionTheory.SquareEuler
