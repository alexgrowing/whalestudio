import Mathlib

noncomputable section

open MvPolynomial

namespace PI.HwFix.UnitaryGroupMassFormula

variable {σ : Type*} {K : Type*} [Field K]

def Ge (w : σ → ℕ) (d : ℕ) : Submodule K (MvPolynomial σ K) where
  carrier := {F | ∀ m, Finsupp.weight w m < d → coeff m F = 0}
  add_mem' := by
    intro F G hF hG
    rw [Set.mem_setOf_eq] at hF hG ⊢
    intro m hm
    rw [coeff_add, hF m hm, hG m hm, add_zero]
  zero_mem' := by
    rw [Set.mem_setOf_eq]
    intro m _
    rw [coeff_zero]
  smul_mem' := by
    intro c F hF
    rw [Set.mem_setOf_eq] at hF ⊢
    intro m hm
    rw [coeff_smul, hF m hm, smul_zero]

theorem mem_Ge {w : σ → ℕ} {d : ℕ} {F : MvPolynomial σ K} :
    F ∈ Ge w d ↔ ∀ m, Finsupp.weight w m < d → coeff m F = 0 := Iff.rfl

theorem Ge_mono {w : σ → ℕ} {d e : ℕ} (h : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ge w e) : F ∈ Ge w d :=
  mem_Ge.2 fun m hm => mem_Ge.1 hF m (lt_of_lt_of_le hm h)

theorem Ge_mul {w : σ → ℕ} {a b : ℕ} {F G : MvPolynomial σ K} (hF : F ∈ Ge w a) (hG : G ∈ Ge w b) :
    F * G ∈ Ge w (a + b) := by
  classical
  rw [mem_Ge] at hF hG ⊢
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h : Finsupp.weight w p.1 + Finsupp.weight w p.2 = Finsupp.weight w m := by rw [← map_add, hp]
  by_cases h1 : Finsupp.weight w p.1 < a
  · rw [hF _ h1, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem monomial_mem_Ge (w : σ → ℕ) (m : σ →₀ ℕ) (c : K) : monomial m c ∈ Ge w (Finsupp.weight w m) := by
  classical
  rw [mem_Ge]
  intro m' hm'
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact lt_irrefl _ hm'

theorem X_mem_Ge (w : σ → ℕ) (v : σ) : (X v : MvPolynomial σ K) ∈ Ge w (w v) := by
  have h := monomial_mem_Ge (K := K) w (Finsupp.single v 1) 1
  rwa [Finsupp.weight_single, one_smul] at h

theorem mul_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) {A B : MvPolynomial σ K} {a b : ℕ}
    (hA : A ∈ Ge w a) (hB : B ∈ Ge w b) (hA' : φ A - A ∈ Ge w (a + 1)) (hB' : φ B - B ∈ Ge w (b + 1)) :
    φ (A * B) - A * B ∈ Ge w (a + b + 1) := by
  have e : φ (A * B) - A * B = (φ A - A) * (φ B - B) + (φ A - A) * B + A * (φ B - B) := by
    rw [map_mul]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact Ge_mono (by omega) (Ge_mul hA' hB')
  · exact Ge_mono (by omega) (Ge_mul hA' hB)
  · exact Ge_mono (by omega) (Ge_mul hA hB')

theorem pow_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (v : σ) (k : ℕ) :
    φ (X v ^ k) - X v ^ k ∈ Ge w (k * w v + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v) := by
      have h := monomial_mem_Ge (K := K) w (Finsupp.single v k) 1
      rwa [Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial] at h
    have h := mul_step w φ hk (X_mem_Ge w v) ih (hφ v)
    have e : (k + 1) * w v + 1 = k * w v + w v + 1 := by ring
    rwa [e]

theorem monomial_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (m : σ →₀ ℕ) :
    φ (monomial m 1) - monomial m 1 ∈ Ge w (Finsupp.weight w m + 1) := by
  induction m using Finsupp.induction with
  | zero => simp
  | single_add v k f _ _ ih =>
    have e : (monomial (Finsupp.single v k + f) (1 : K)) = X v ^ k * monomial f 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [e]
    have hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v) := by
      have h := monomial_mem_Ge (K := K) w (Finsupp.single v k) 1
      rwa [Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial] at h
    have h := mul_step w φ hk (monomial_mem_Ge w f 1) (pow_step w φ hφ v k) ih
    rwa [map_add, Finsupp.weight_single, smul_eq_mul]

theorem uni_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (d : ℕ) (F : MvPolynomial σ K) (hF : F ∈ Ge w d) :
    φ F - F ∈ Ge w (d + 1) := by
  have key : ∀ m ∈ F.support, φ (monomial m (coeff m F)) - monomial m (coeff m F) ∈ Ge w (d + 1) := by
    intro m hm
    have hd : d ≤ Finsupp.weight w m := by
      by_contra h
      exact (mem_support_iff.mp hm) (mem_Ge.1 hF m (by omega))
    have e : monomial m (coeff m F) = coeff m F • monomial m (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (Ge_mono (by omega) (monomial_step w φ hφ m))
  have h := Submodule.sum_mem _ key
  rwa [Finset.sum_sub_distrib, ← map_sum, ← F.as_sum] at h

theorem coeffs_mem [Infinite K] {V : Type*} [AddCommGroup V] [Module K V] (S : Submodule K V) (N : ℕ) (f : ℕ → V)
    (h : ∀ s : K, s ≠ 0 → ∑ k ∈ Finset.range N, s ^ k • f k ∈ S) (k : ℕ) (hk : k < N) : f k ∈ S := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro ψ
  let p : Polynomial K := ∑ j ∈ Finset.range N, Polynomial.C (ψ (Submodule.Quotient.mk (f j))) * Polynomial.X ^ j
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ ((Set.finite_singleton (0 : K)).infinite_compl)
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    have h1 : S.mkQ (∑ k ∈ Finset.range N, s ^ k • f k) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (h s hs)
    have h2 := congrArg ψ h1
    rw [map_sum, map_sum, map_zero] at h2
    simp only [map_smul, Submodule.mkQ_apply, smul_eq_mul] at h2
    show Polynomial.IsRoot p s
    rw [Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have h3 := congrArg (fun q => Polynomial.coeff q k) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero, Polynomial.coeff_zero] at h3
  rw [Finset.sum_ite_eq] at h3
  simpa [Finset.mem_range.mpr hk] using h3

def sc (w : σ → ℕ) (c : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun v => C (c ^ w v) * X v

theorem sc_monomial (w : σ → ℕ) (c : K) (m : σ →₀ ℕ) (a : K) :
    sc w c (monomial m a) = monomial m (c ^ Finsupp.weight w m * a) := by
  classical
  rw [sc, aeval_monomial]
  simp only [mul_pow, Finsupp.prod_mul]
  have h1 : (m.prod fun v k => (C (c ^ w v) : MvPolynomial σ K) ^ k) = C (c ^ Finsupp.weight w m) := by
    simp only [← C_pow, ← map_finsuppProd]
    congr 1
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [monomial_eq, algebraMap_eq, C_mul, h1]
  ring

theorem coeff_sc (w : σ → ℕ) (c : K) (F : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (sc w c F) = c ^ Finsupp.weight w m * coeff m F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum]
  simp only [sc_monomial, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, mul_zero]

theorem sc_eq_sum (w : σ → ℕ) (c : K) (F : MvPolynomial σ K) (N : ℕ)
    (hN : ∀ m ∈ F.support, Finsupp.weight w m < N) :
    sc w c F = ∑ k ∈ Finset.range N, c ^ k • weightedHomogeneousComponent w k F := by
  classical
  ext m
  rw [coeff_sc, coeff_sum]
  simp only [coeff_smul, coeff_weightedHomogeneousComponent, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_cases hm : m ∈ F.support
    · exact absurd (Finset.mem_range.mpr (hN m hm)) h
    · rw [notMem_support_iff.mp hm, mul_zero]

end PI.HwFix.UnitaryGroupMassFormula
