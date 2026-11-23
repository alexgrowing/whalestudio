import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PjCong

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

theorem sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : sgn ε i * sgn ε i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem star_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : star (sgn ε i) = sgn ε i := by
  unfold sgn
  split_ifs <;> simp

theorem star_I' : star Complex.I = -Complex.I := Complex.conj_I

theorem norm_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ‖sgn ε i‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem lie_apply {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M) i j = star (M j i) * sgn ε j + sgn ε i * M i j := by
  simp only [Matrix.add_apply, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, sgn]

def cpx {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a : Fin k) (b : Fin m) : ℂ :=
  ⟨u (a, b, true), u (a, b, false)⟩

theorem cpx_add {k m : ℕ} (u v : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (u + v) a b = cpx u a b + cpx v a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_smul {k m : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (c • u) a b = (c : ℂ) * cpx u a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_eq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    Matrix.of (cpx u) = Matrix.of ((reimE (r := k) (m := m)).symm u) := rfl

theorem cpx_reim {k m : ℕ} (Y : Matrix (Fin k) (Fin m) ℂ) (a b) : cpx (reim Y) a b = Y a b := by
  apply Complex.ext <;> simp [cpx, reim]

theorem norm_cpx_sq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    ‖u‖ ^ 2 = ∑ a, ∑ b, ‖cpx u a b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [cpx, Real.norm_eq_abs, sq]

def r2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem inv_sqrt_two_mul : r2 * (Real.sqrt 2 : ℂ) = 1 := by
  rw [r2, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr two_pos), Complex.ofReal_one]

theorem norm_inv_sqrt_two_sq : ‖r2‖ ^ 2 = 1 / 2 := by
  rw [r2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

variable {n k m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S})
  (eU : Fin m ≃ {i // i ∉ S}) {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)

def xiF (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if hi : i ∈ S then (if hj : j ∈ S then 0 else r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))
    else (if hj : j ∈ S then -(sgn ε i * sgn ε j) * star (r2 * cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩))
      else sgn ε i * Complex.I * H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))

def xiL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := xiF ε S eS eU H
  map_add' a b := by
    ext i j
    simp only [xiF, Matrix.add_apply]
    split_ifs <;> (try simp [cpx_add]) <;> ring
  map_smul' c z := by
    ext i j
    simp only [xiF, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [cpx_smul, Complex.real_smul, Complex.conj_ofReal]) <;> ring

theorem xi_SS (z) (a b : Fin k) : xiF ε S eS eU H z (eS a) (eS b) = 0 := by
  simp [xiF, (eS a).2, (eS b).2]

theorem xi_SU (z) (a : Fin k) (b : Fin m) : xiF ε S eS eU H z (eS a) (eU b) = r2 * cpx z.1 a b := by
  simp [xiF, (eS a).2, (eU b).2]

theorem xi_US (z) (a : Fin m) (b : Fin k) :
    xiF ε S eS eU H z (eU a) (eS b) = -(sgn ε (eU a) * sgn ε (eS b)) * star (r2 * cpx z.1 b a) := by
  simp [xiF, (eU a).2, (eS b).2]

theorem xi_UU (z) (a b : Fin m) : xiF ε S eS eU H z (eU a) (eU b) = sgn ε (eU a) * Complex.I * H z.2 a b := by
  simp [xiF, (eU a).2, (eU b).2]

theorem sum_split {M : Type} [AddCommMonoid M] (f : Fin n → M) : ∑ i, f i = ∑ a, f (eS a) + ∑ a, f (eU a) := by
  have h : ∑ i, f i = ∑ x : ↥S, f ↑x + ∑ x : {i // i ∉ S}, f ↑x := by
    convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f).symm
  exact h.trans (congrArg₂ (· + ·) (eS.sum_comp (fun x => f x)).symm (eU.sum_comp (fun x => f x)).symm)

theorem xi_norm (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (z) :
    ∑ i, ∑ j, ‖xiF ε S eS eU H z i j‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp only [sum_split S eS eU, xi_SS, xi_SU, xi_US, xi_UU, norm_zero, norm_mul, norm_neg, norm_star,
    norm_sgn, Complex.norm_I, mul_pow, norm_inv_sqrt_two_sq, one_mul, mul_one]
  rw [norm_cpx_sq z.1, ← hn z.2]
  have hc : ∑ x : Fin m, ∑ y : Fin k, ‖cpx z.1 y x‖ ^ 2 = ∑ y : Fin k, ∑ x : Fin m, ‖cpx z.1 y x‖ ^ 2 :=
    Finset.sum_comm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  ring

theorem xi_mem (hH : ∀ t, (H t)ᴴ = H t) (z) :
    (xiF ε S eS eU H z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * xiF ε S eS eU H z = 0 ∧
      ∀ i ∈ S, ∀ j ∈ S, xiF ε S eS eU H z i j = 0 := by
  refine ⟨?_, fun i hi j hj => by simp [xiF, hi, hj]⟩
  have hHe : ∀ a b, star (H z.2 b a) = H z.2 a b := fun a b => by
    have h := congrFun (congrFun (hH z.2) a) b
    rwa [Matrix.conjTranspose_apply] at h
  ext i j
  rw [lie_apply, Matrix.zero_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, star_mul', star_neg, star_star, star_sgn]
    linear_combination (-(sgn ε i) * (r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j
  · simp only [xiF, dif_pos hj, dif_neg hi, star_mul']
    linear_combination (-(sgn ε j) * (star r2 * star (cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩)))) * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, star_mul', star_sgn, star_I', hHe]
    linear_combination (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε i - (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j

theorem xi_onto (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (ξ : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ξᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ξ = 0) (h2 : ∀ i ∈ S, ∀ j ∈ S, ξ i j = 0) :
    ∃ z, xiF ε S eS eU H z = ξ := by
  have hξ : ∀ i j, star (ξ j i) * sgn ε j + sgn ε i * ξ i j = 0 := fun i j => by
    have h := congrFun (congrFun h1 i) j
    rwa [lie_apply, Matrix.zero_apply] at h
  let u : EuclideanSpace ℝ (Fin k × Fin m × Bool) :=
    reim (Matrix.of fun a b => (Real.sqrt 2 : ℂ) * ξ (eS a) (eU b))
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => -Complex.I * sgn ε (eU a) * ξ (eU a) (eU b)
  have hM : Mᴴ = M := by
    ext a b
    simp only [M, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_neg, star_I', star_sgn]
    linear_combination Complex.I * hξ (eU a) (eU b)
  obtain ⟨t, ht⟩ := hs M hM
  have e2 : ∀ w : ℂ, r2 * ((Real.sqrt 2 : ℂ) * w) = w := fun w => by rw [← mul_assoc, inv_sqrt_two_mul, one_mul]
  refine ⟨(u, t), ?_⟩
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj, h2 i hi j hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
  · simp only [xiF, dif_neg hi, dif_pos hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
    linear_combination (-(sgn ε i)) * hξ i j + ξ i j * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, ht, M, Matrix.of_apply, Equiv.apply_symm_apply]
    linear_combination (-(sgn ε i) ^ 2 * ξ i j) * Complex.I_sq + ξ i j * sgn_mul_self ε i

theorem dom_exists {ι : Type} [Fintype ι] (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0)
    (hnL : ∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2)
    (hLs : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M)
    (hH : ∀ t, (H t)ᴴ = H t) (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    ∃ Λ : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι,
      MeasurePreserving Λ volume volume ∧ ∀ z, L (Λ z) = xiF ε S eS eU H z := by
  have hxi : ∀ z, ∃ x, L x = xiL ε S eS eU H z := fun z =>
    hLs _ (xi_mem ε S eS eU H hH z).1 (xi_mem ε S eS eU H hH z).2
  let Λ := liftL L (inj_of_frob L hnL) (xiL ε S eS eU H) hxi
  have hΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z := fun z => liftL_spec L (inj_of_frob L hnL) _ hxi z
  refine ⟨Λ, mp_of_isom_prod Λ (fun a b => ?_) ?_, hΛ⟩
  · rw [← hnL, hΛ]
    exact xi_norm ε S eS eU H hnH (a, b)
  · intro x
    obtain ⟨z, hz⟩ := xi_onto ε S eS eU H hsH (L x) (hL x).1 (hL x).2
    exact ⟨z, inj_of_frob L hnL ((hΛ z).trans hz)⟩

end PI.AprimeInfW
