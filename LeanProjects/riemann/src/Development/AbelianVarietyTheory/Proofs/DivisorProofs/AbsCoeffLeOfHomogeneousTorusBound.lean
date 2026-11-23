import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.CoefTorus

theorem sum_eq_of_coeff_ne_zero {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    {d : Fin n →₀ ℕ} (hd : coeff d T ≠ 0) : ∑ i, d i = q := by
  have := hT hd
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this

theorem aeval_smul_of_homogeneous {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    (c : ℂ) (z : Fin n → ℂ) : aeval (c • z) T = c ^ q * aeval z T := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
  ring

theorem geom_root {N m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (h0 : 0 < m) (h2 : m < 2 * N) :
    ∑ j : Fin N, (ζ ^ m) ^ (j : ℕ) = if m = N then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) N]
  split_ifs with hm
  · subst hm; simp [hζ.pow_eq_one]
  · have hne : ζ ^ m ≠ 1 := by
      rw [Ne, hζ.pow_eq_one_iff_dvd]
      rintro ⟨c, hc⟩
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem key_sum {n q N : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (α : Fin n →₀ ℕ) (hq : q < N) (hα : ∀ i, α i < N) :
    ∑ k : Fin n → Fin N, aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = ((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ n := by
  have inner : ∀ d ∈ T.support, ∑ k : Fin n → Fin N,
      (algebraMap ℤ ℂ (coeff d T) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = if d = α then ((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ n else 0 := by
    intro d hd
    have hdq : ∀ i, d i ≤ q := fun i => by
      rw [← sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
      exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have e1 : ∑ k : Fin n → Fin N,
        (algebraMap ℤ ℂ (coeff d T) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
        = algebraMap ℤ ℂ (coeff d T) * ∏ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ) := by
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
    rw [e1]
    have e2 : ∀ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ)
        = if d i = α i then (N : ℂ) else 0 := by
      intro i
      rw [geom_root hζ (by have := hα i; omega) (by have := hα i; have := hdq i; omega)]
      have := hα i; have := hdq i
      by_cases h : d i = α i
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [e2]
    by_cases h : d = α
    · subst h; simp [Finset.prod_const, Finset.card_univ]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ α i := by
        by_contra hc; push_neg at hc; exact h (Finsupp.ext hc)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi]), mul_zero]
  simp_rw [aeval_def, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have h0 : coeff α T = 0 := not_not.mp (mt MvPolynomial.mem_support_iff.mpr h)
    simp [h0]

theorem coeff_le_of_torus_bound : ∀ (D q : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ) (M : ℝ), T.IsHomogeneous q →
    (∀ z : Fin (D + 1) → ℂ, z 0 = 1 → (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M) →
    ∀ α, |((coeff α T : ℤ) : ℝ)| ≤ M := by
  intro D q T M hT hM α
  have htor : ∀ z : Fin (D + 1) → ℂ, (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M := by
    intro z hz
    have h0 : z 0 ≠ 0 := by
      intro h; have := hz 0; simp [h] at this
    have hb := hM ((z 0)⁻¹ • z) (by simp [h0]) (by intro l; simp [norm_inv, hz])
    have e : z = z 0 • ((z 0)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    rw [e, aeval_smul_of_homogeneous hT, norm_mul, norm_pow, hz 0, one_pow, one_mul]
    exact hb
  set N := q + (∑ i, α i) + 1 with hN
  have hNpos : N ≠ 0 := by omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) N :=
    Complex.isPrimitiveRoot_exp N hNpos
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hNpos
  have hα : ∀ i, α i < N := fun i => by
    have := Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have key := key_sum hT hζ α (by omega) hα
  have hbound : ‖((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ (D + 1)‖ ≤ (N : ℝ) ^ (D + 1) * M := by
    rw [← key]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k : Fin (D + 1) → Fin N,
        ‖aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)‖ ≤ M := by
      intro k
      rw [norm_mul, norm_prod]
      simp only [norm_pow, hζn, one_pow, Finset.prod_const_one, mul_one]
      exact htor _ (fun l => by simp [hζn])
    refine (Finset.sum_le_sum fun k _ => this k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; exact le_refl _
  rw [norm_mul, norm_pow, Complex.norm_natCast, mul_comm] at hbound
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
  have := le_of_mul_le_mul_left hbound hpos
  simpa [Complex.norm_intCast] using this

end GlobalTheory.HSAmp.CoefTorus
