import Mathlib

open MvPolynomial

namespace GlobalTheory.MxDet

noncomputable def linF {ι : Type} [Fintype ι] (x : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.X i

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_linF {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (linF x) = MvPolynomial.C (x j) := by
  rw [linF, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_linF_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (linF x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * linF x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_linF_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_linF, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (linF x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_linF_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem det_comb {ι : Type} [Fintype ι] (e : ℕ) (H : ι → Matrix (Fin e) (Fin e) ℂ) (x : ι → ℝ) :
    (∑ i, (x i : ℂ) • H i).det = ∑ c : Fin e → ι, ((∏ l, x (c l) : ℝ) : ℂ) *
      ∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l := by
  rw [Matrix.det_apply']
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

end GlobalTheory.MxDet

theorem GlobalTheory.MxDet.re_det_relation : ∀ (ι J : Type) [Fintype ι] [Fintype J] (e : ℕ) (a : J → ℝ) (n : J → ι → ℝ), ∑ j, MvPolynomial.C (a j) * (∑ i, MvPolynomial.C (n j i) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 → ∀ H : ι → Matrix (Fin e) (Fin e) ℂ, ∑ j, a j * (∑ i, (n j i : ℂ) • H i).det.re = 0 := by
  intro ι J _ _ e a n hrel H
  obtain ⟨T, hT⟩ := GlobalTheory.MxDet.exists_functional e fun c : Fin e → ι =>
    (∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l).re
  have h := congrArg T hrel
  simp only [map_sum, map_zero, MvPolynomial.C_mul', LinearMap.map_smul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := hT (n j)
  simp only [GlobalTheory.MxDet.linF, MvPolynomial.C_mul'] at this
  rw [this, GlobalTheory.MxDet.det_comb, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_ofReal_mul]
