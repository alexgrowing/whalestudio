import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacC

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem map_star_eq (U : Matrix (Fin n) (Fin n) ℂ) : U.map star = (Uᴴ)ᵀ := by
  ext i j; simp [conjTranspose_apply]

theorem normSq_det_unitary {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    Complex.normSq U.det = 1 := by
  have h := congrArg Matrix.det (mem_unitaryGroup_iff'.mp hU)
  rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose] at h
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  simpa using h

theorem mp_cU {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun w : Fin n → ℂ => (U.map star) *ᵥ w) volume volume := by
  set L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' (U.map star)).restrictScalars ℝ with hLdef
  have hdet : LinearMap.det L = 1 := by
    rw [hLdef, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, map_star_eq,
      det_transpose, det_conjTranspose]
    show Complex.normSq (star U.det) = 1
    rw [Complex.star_def, Complex.normSq_conj, normSq_det_unitary hU]
  have hmeas : Measurable (fun w : Fin n → ℂ => (U.map star) *ᵥ w) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hmeas, ?_⟩
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

def rowF (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  Complex.exp (-(c * ∑ i, ‖v i‖ ^ 2 : ℝ)) * Complex.exp (Complex.I * κ * ∑ i, ∑ j, b i j * star (v j) * v i)

theorem sumsq_eq (v : Fin n → ℂ) : (((∑ i, ‖v i‖ ^ 2 : ℝ)) : ℂ) = star v ⬝ᵥ v := by
  push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem quad_eq (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ∑ i, ∑ j, b i j * star (v j) * v i = v ⬝ᵥ (b *ᵥ star v) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowF_comp (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) (w : Fin n → ℂ) :
    rowF c κ b ((hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).map star *ᵥ w) =
      ∏ k, Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖w k‖ : ℂ) ^ 2) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem hb.eigenvectorUnitary.2
  have hT : Uᵀ * U.map star = 1 := by
    rw [map_star_eq, ← transpose_mul, hUU, transpose_one]
  have key : ∀ x : Fin n → ℂ, (U *ᵥ x) ⬝ᵥ (U.map star *ᵥ w) = x ⬝ᵥ w := by
    intro x
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hT, vecMul_one]
  have hstar : star (U.map star *ᵥ w) = U *ᵥ star w := by
    ext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  have hbU : b * U = U * diagonal (RCLike.ofReal ∘ hb.eigenvalues) := by
    conv_lhs => rw [hb.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_assoc, star_eq_conjTranspose, hUU, Matrix.mul_one]
  have hS : ∑ i, ‖(U.map star *ᵥ w) i‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    have h := sumsq_eq (U.map star *ᵥ w)
    rw [hstar, key, ← sumsq_eq] at h
    exact_mod_cast h
  have hQ : ∑ i, ∑ j, b i j * star ((U.map star *ᵥ w) j) * (U.map star *ᵥ w) i =
      ∑ k, (hb.eigenvalues k : ℂ) * (‖w k‖ : ℂ) ^ 2 := by
    rw [quad_eq, dotProduct_comm, hstar, mulVec_mulVec, hbU, ← mulVec_mulVec, key]
    simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.star_def, Complex.conj_mul']
    rfl
  rw [rowF, hS, hQ, ← Complex.exp_add, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem det_shift (c κ : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    ((c : ℂ) • 1 - (Complex.I * κ) • b).det = ∏ k, ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
  have hX : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * κ) • diagonal (RCLike.ofReal ∘ hb.eigenvalues) =
      diagonal (fun k => (c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [one_apply, h]
  have hD : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * κ) • b =
      Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary
        ((c : ℂ) • 1 - (Complex.I * κ) • diagonal (RCLike.ofReal ∘ hb.eigenvalues)) := by
    conv_lhs => rw [hb.spectral_theorem]
    rw [map_sub, map_smul, map_smul, map_one]
  have hu : (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).det *
      (star (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [← det_mul, Unitary.mul_star_self_of_mem hb.eigenvectorUnitary.2, det_one]
  rw [hD, Unitary.conjStarAlgAut_apply, hX, det_mul, det_mul, det_diagonal, mul_right_comm, hu, one_mul]

theorem row_int (c κ : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    ∫ v : Fin n → ℂ, rowF c κ b v = (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * κ) • b).det := by
  have mp := mp_cU hb.eigenvectorUnitary.2
  have hcont : Continuous (rowF c κ b) := by
    unfold rowF
    fun_prop
  have hg : ∀ k, ∫ z : ℂ, Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖z‖ : ℂ) ^ 2) =
      (Real.pi : ℂ) / ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) := by
    intro k
    have ha : 0 < ((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)).re := by simp [hc]
    have h := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) ha
    rw [Complex.finrank_real_complex] at h
    simpa using h
  rw [← mp.map_eq, integral_map mp.measurable.aemeasurable hcont.aestronglyMeasurable]
  simp_rw [rowF_comp c κ b hb]
  have hprod := integral_fintype_prod_eq_prod
    (f := fun k (z : ℂ) => Complex.exp (-((c : ℂ) - Complex.I * κ * (hb.eigenvalues k : ℂ)) * (‖z‖ : ℂ) ^ 2))
    (μ := fun _ : Fin n => (volume : Measure ℂ))
  rw [← volume_pi] at hprod
  rw [hprod, Finset.prod_congr rfl (fun k _ => hg k), Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, det_shift c κ b hb]

end PositivityTheory.Rg.Sw.Glob.Vac
