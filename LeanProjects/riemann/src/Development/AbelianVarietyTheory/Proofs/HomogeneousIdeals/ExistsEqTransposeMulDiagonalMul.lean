import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv

open Complex Matrix MeasureTheory
open scoped Real

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped MatrixOrder in

theorem IsSiegel.exists_eq_transpose_mul_diagonal_mul {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ P : Matrix ι ι ℝ, P.det ≠ 0 ∧ ∃ t : ι → ℂ, (∀ i, 0 < (t i).im) ∧
      σ = (P.map ofReal)ᵀ * diagonal t * P.map ofReal := by
  obtain ⟨B, hB, hY⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    h.posDef.isStrictlyPositive
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hY
  have hB' : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB
  have hX : (σ.map Complex.re).IsHermitian := by
    ext i j
    simp [conjTranspose_apply, h.isSymm.apply]
  have hX' : (B⁻¹ᴴ * σ.map Complex.re * B⁻¹).IsHermitian := isHermitian_conjTranspose_mul_mul _ hX
  obtain ⟨U, l, hUU, hs⟩ : ∃ (U : Matrix ι ι ℝ) (l : ι → ℝ), U * Uᵀ = 1 ∧
      B⁻¹ᵀ * σ.map Complex.re * B⁻¹ = U * diagonal l * Uᵀ :=
    ⟨hX'.eigenvectorUnitary.1, hX'.eigenvalues, Unitary.coe_mul_star_self hX'.eigenvectorUnitary,
      hX'.spectral_theorem⟩
  refine ⟨Uᵀ * B, ?_, fun i => l i + I, fun i => by simp, ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (isUnit_det_of_right_inverse hUU).ne_zero hB'.ne_zero
  have e1 : σ.map Complex.re = (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) := by
    have : (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) =
        Bᵀ * (U * diagonal l * Uᵀ) * B := by
      simp [Matrix.mul_assoc]
    rw [this, ← hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul,
      nonsing_inv_mul _ hB', transpose_one, Matrix.one_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hB', Matrix.mul_one]
  have e2 : σ.map Complex.im = (Uᵀ * B)ᵀ * (Uᵀ * B) := by
    rw [hY, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU,
      Matrix.one_mul]
  generalize Uᵀ * B = P at e1 e2
  ext i j
  have e1' := congrFun (congrFun e1 i) j
  have e2' := congrFun (congrFun e2 i) j
  simp only [mul_apply, map_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1' e2' ⊢
  apply Complex.ext <;> simp [e1', e2']

omit [DecidableEq ι] in

theorem ofReal_mulVec_eq (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    (fun i => ((P *ᵥ x) i : ℂ)) = P.map ofReal *ᵥ fun i => (x i : ℂ) := by
  ext i
  simp [mulVec, dotProduct]

theorem isUnit_det_map_ofReal {P : Matrix ι ι ℝ} (hP : P.det ≠ 0) :
    IsUnit (P.map ofReal).det := by
  have : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
  rw [this]
  simpa using hP

theorem inv_map_ofReal {P : Matrix ι ι ℝ} (hP : P.det ≠ 0) :
    (P.map ofReal)⁻¹ = P⁻¹.map ofReal := by
  refine inv_eq_right_inv ?_
  change P.map ofRealHom * P⁻¹.map ofRealHom = 1
  rw [← Matrix.map_mul, mul_nonsing_inv _ hP.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem IsSiegel.transpose_mul_mul {σ : Matrix ι ι ℂ} (h : IsSiegel σ) {P : Matrix ι ι ℝ}
    (hP : P.det ≠ 0) : IsSiegel ((P.map ofReal)ᵀ * σ * P.map ofReal) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isSymm.eq,
      Matrix.mul_assoc]
  · convert h.posDef.conjTranspose_mul_mul_same (B := P)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det P).2 hP.isUnit)) using 1
    ext i j
    simp [mul_apply]

theorem IsSiegel.isUnit_det {σ : Matrix ι ι ℂ} (h : IsSiegel σ) : IsUnit σ.det := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  rw [det_mul, det_mul, det_transpose, det_diagonal]
  refine ((isUnit_det_map_ofReal hP).mul (IsUnit.mk0 _ ?_)).mul (isUnit_det_map_ofReal hP)
  exact Finset.prod_ne_zero_iff.2 fun i _ h0 => by simpa [h0] using ht i

theorem inv_diagonal_of_ne_zero {t : ι → ℂ} (ht : ∀ i, t i ≠ 0) :
    (diagonal t)⁻¹ = diagonal fun i => (t i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  exact funext fun i => mul_inv_cancel₀ (ht i)

theorem IsSiegel.neg_inv {σ : Matrix ι ι ℂ} (h : IsSiegel σ) : IsSiegel (-σ⁻¹) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have h1 : IsSiegel (diagonal fun i => -(t i)⁻¹) := isSiegel_diagonal_iff.2 fun i => by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (ht i) (normSq_pos.2 (ht0 i))
  have h2 : (P⁻¹ᵀ).det ≠ 0 := by
    rw [det_transpose]
    exact (isUnit_nonsing_inv_det _ hP.isUnit).ne_zero
  convert h1.transpose_mul_mul h2 using 1
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
    ← transpose_nonsing_inv, inv_map_ofReal hP, transpose_map, transpose_transpose,
    ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in

theorem IsSiegel.add_map_ofReal {σ : Matrix ι ι ℂ} (h : IsSiegel σ) {C : Matrix ι ι ℝ}
    (hC : C.IsSymm) : IsSiegel (σ + C.map ofReal) := by
  refine ⟨h.isSymm.add (hC.map _), ?_⟩
  convert h.posDef using 1
  ext i j
  simp

def siegelGaussIntegral {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) : ℂ :=
  ∫ x : ι → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))))

theorem integral_comp_mulVec_of_det_ne_zero {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    ∫ x, f (P *ᵥ x) = (|P.det⁻¹| : ℝ) * ∫ y, f y := by
  have h := integral_map (μ := (volume : Measure (ι → ℝ))) (φ := toLin' P) (f := f)
    (toLin' P).continuous_of_finiteDimensional.measurable.aemeasurable hf.aestronglyMeasurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hP, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), real_smul] at h
  rw [h]
  rfl

theorem IsSiegel.exists_integral_cexp_quadratic {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ s : ℂ, s ^ 2 * (-I • σ).det = 1 ∧ ∀ w : ι → ℂ,
      ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) = s * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu := isUnit_det_map_ofReal hP
  refine ⟨(|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ), ?_, fun w => ?_⟩
  · have e : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
    have e2 (i : ι) : ((π / (-(π * I * t i))) ^ (1 / 2 : ℂ)) ^ 2 * (-I * t i) = 1 := by
      rw [one_div, cpow_ofNat_inv_pow]
      field_simp [ht0 i]
    have e3 : (P.det : ℂ) ≠ 0 := by exact_mod_cast hP
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul, det_mul, det_mul, det_transpose,
      det_diagonal, e, mul_pow, ← ofReal_pow, sq_abs, ← Finset.prod_pow]
    have e4 := Finset.prod_congr (s₁ := Finset.univ) rfl fun i _ => e2 i
    rw [Finset.prod_mul_distrib, Finset.prod_const_one] at e4
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    have e5 : (P.det : ℂ)⁻¹ ^ 2 * P.det * P.det = 1 := by field_simp
    linear_combination ((P.det : ℂ)⁻¹ ^ 2 * P.det * P.det) * e4 + e5
  set v := ((P.map ofReal)ᵀ)⁻¹ *ᵥ w with hv
  have hw : w = (P.map ofReal)ᵀ *ᵥ v := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_transpose _ hu), one_mulVec]
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun i => 2 * π * I * v i
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, 2 * π * I * v i * y i)) (by fun_prop)
  rw [key, Finset.prod_mul_distrib, ← Complex.exp_sum, ← mul_assoc] at hc
  convert hc using 3 with x
  · congr 1
    have e := ofReal_mulVec_eq P x
    rw [hw, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec _ _ v,
      vecMul_transpose, ← e]
    simp only [dotProduct, mulVec_diagonal, Finset.sum_div, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hv, dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, ← hv]
    simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [ht0 i]
    ring

theorem IsSiegel.integral_cexp_quadratic {σ : Matrix ι ι ℂ} (h : IsSiegel σ) (w : ι → ℂ) :
    ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) =
      siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨s, -, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := hs 0
  simp only [dotProduct_zero, zero_dotProduct, add_zero, mul_zero, Complex.exp_zero,
    mul_one] at h0
  rw [hs, ← h0, siegelGaussIntegral]
  congr 2 with x
  ring_nf

theorem IsSiegel.siegelGaussIntegral_sq_mul_det {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    siegelGaussIntegral σ ^ 2 * (-I • σ).det = 1 := by
  obtain ⟨s, hs1, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := (h.integral_cexp_quadratic 0).symm.trans (hs 0)
  rw [mul_left_inj' (Complex.exp_ne_zero _)] at h0
  rwa [h0]

theorem IsSiegel.siegelGaussIntegral_ne_zero {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    siegelGaussIntegral σ ≠ 0 := fun h0 => by
  simpa [h0] using h.siegelGaussIntegral_sq_mul_det

theorem tsum_poisson_pi_int {f F : (ι → ℝ) → ℂ} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : (ι → ℤ) → ℝ, Summable g ∧ ∀ (n : ι → ℤ) (u : ι → ℝ), ‖u‖ ≤ R →
      ‖f ((fun i => (n i : ℝ)) + u)‖ ≤ g n)
    (hF : ∀ y : ι → ℝ, ∫ x : ι → ℝ,
      cexp (-(2 * π * I) * ((fun i => (x i : ℂ)) ⬝ᵥ fun i => (y i : ℂ))) * f x = F y)
    (hs : Summable fun n : ι → ℤ => ‖F fun i => (n i : ℝ)‖) (u : ι → ℝ) :
    ∑' n : ι → ℤ, f ((fun i => (n i : ℝ)) + u) =
      ∑' n : ι → ℤ, cexp (2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (u i : ℂ))) *
        F fun i => (n i : ℝ) := by
  set L : Submodule ℤ (EuclideanSpace ℝ ι) :=
    Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) with hL
  have hmem (x : EuclideanSpace ℝ ι) : x ∈ L ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = x k := by
    rw [hL, Module.Basis.mem_span_iff_repr_mem]
    simp
  have hmem' (y : EuclideanSpace ℝ ι) : y ∈ dualLattice L ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = y k := by
    rw [mem_dualLattice]
    refine ⟨fun h k => ?_, fun h x hx => ?_⟩
    · simpa [EuclideanSpace.inner_single_left] using h _ (Submodule.subset_span ⟨k, rfl⟩)
    · choose a ha using (hmem x).1 hx
      choose b hb using h
      exact ⟨∑ k, b k * a k, by simp [PiLp.inner_apply, ha, hb]⟩
  have hequiv (M : Submodule ℤ (EuclideanSpace ℝ ι))
      (hM : ∀ x, x ∈ M ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = x k) :
      ∃ e : (ι → ℤ) ≃ M, ∀ n, (e n : EuclideanSpace ℝ ι) = WithLp.toLp 2 fun i => (n i : ℝ) := by
    refine ⟨Equiv.ofBijective (fun n => ⟨WithLp.toLp 2 fun i => (n i : ℝ),
      (hM _).2 fun k => ⟨n k, rfl⟩⟩) ⟨fun n m h => funext fun i => ?_, fun x => ?_⟩, fun _ => rfl⟩
    · simpa using congrArg (fun x : M => (x : EuclideanSpace ℝ ι) i) h
    · choose a ha using (hM x).1 x.2
      exact ⟨a, Subtype.ext (by ext i; exact ha i)⟩
  obtain ⟨e, he⟩ := hequiv L hmem
  obtain ⟨e', he'⟩ := hequiv _ hmem'
  have hF' (y : ι → ℝ) : FourierTransform.fourier (fun x : EuclideanSpace ℝ ι => f x.ofLp)
      (WithLp.toLp 2 y) = F y := by
    rw [Real.fourier_eq', ← hF, ← (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    congr 1 with x
    rw [smul_eq_mul]
    congr 2
    simp only [PiLp.inner_apply, dotProduct, RCLike.inner_apply, conj_trivial, mul_comm (y _)]
    push_cast
    ring
  have key := tsum_poisson_lattice L (f := fun x : EuclideanSpace ℝ ι => f x.ofLp) (by fun_prop)
    (fun R => by
      obtain ⟨g, hg, h⟩ := hdom R
      refine ⟨g ∘ e.symm, e.symm.summable_iff.2 hg, fun x v hv => ?_⟩
      obtain ⟨n, rfl⟩ := e.surjective x
      rw [he, Function.comp_apply, e.symm_apply_apply]
      refine h n v.ofLp ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hv)).2 fun i => ?_)
      exact (PiLp.norm_apply_le v i).trans hv)
    (by
      rw [← e'.summable_iff]
      simpa only [Function.comp_def, he', hF'] using hs) (WithLp.toLp 2 u)
  rw [← e.tsum_eq, ← e'.tsum_eq, covolume_span_basis (EuclideanSpace.basisFun ι ℝ),
    Module.Basis.det_self] at key
  simp only [he, he', hF', abs_one, inv_one, one_smul, smul_eq_mul] at key
  refine key.trans (tsum_congr fun n => ?_)
  congr 3
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem IsSiegel.riemannTheta_eq_neg_inv {σ : Matrix ι ι ℂ} (h : IsSiegel σ) (a : ι → ℝ)
    (w : ι → ℂ) :
    riemannTheta a 0 σ w = siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) *
      riemannTheta 0 a (-σ⁻¹) (σ⁻¹ *ᵥ w) := by
  have hsi : σ⁻¹.IsSymm := by rw [Matrix.IsSymm, transpose_nonsing_inv, h.isSymm.eq]
  set f : (ι → ℝ) → ℂ := fun x => cexp (2 * π * I *
    (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 + (fun i => (x i : ℂ)) ⬝ᵥ w)) with hf
  have hc : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hfn (n : ι → ℤ) (u : ι → ℝ) :
      f ((fun i => (n i : ℝ)) + u) = riemannThetaTerm u 0 σ w n := by
    simp [hf, riemannThetaTerm_def]
  have key := tsum_poisson_pi_int (f := f) (F := fun y => siegelGaussIntegral σ *
      cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) * cexp (2 * π * I *
      (((fun i => (y i : ℂ)) ⬝ᵥ (-σ⁻¹ *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ (σ⁻¹ *ᵥ w)))) hc (fun R => ?_) (fun y => ?_) ?_ a
  · simp only [hfn] at key
    rw [riemannTheta, key, riemannTheta, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have := riemannThetaTerm_add_ofReal 0 0 a (-σ⁻¹) (σ⁻¹ *ᵥ w) n
    rw [zero_add] at this
    rw [← this, riemannThetaTerm_add, riemannThetaTerm_zero_zero]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, ofReal_intCast]
    ring
  · obtain ⟨c, hc0, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ι → ℝ) R).exists_bound_of_continuousOn
      hc.continuousOn
    obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : ι → ℝ) R).exists_bound_of_continuousOn
      (f := fun u => w + σ *ᵥ fun i => (u i : ℂ)) (Continuous.continuousOn (by
        refine continuous_const.add (continuous_pi fun i => ?_)
        simp only [mulVec, dotProduct]
        fun_prop))
    refine ⟨_, (summable_riemannThetaBound 0 hc0 S).mul_left M, fun n u hu => ?_⟩
    have hu' := mem_closedBall_zero_iff.2 hu
    have e : riemannThetaTerm u 0 σ w n =
        f u * riemannThetaTerm 0 0 σ (w + σ *ᵥ fun i => (u i : ℂ)) n := by
      rw [riemannThetaTerm_add_mulVec_ofReal h.isSymm, ← mul_assoc, hf, ← Complex.exp_add]
      simp
    rw [hfn, e, norm_mul]
    exact mul_le_mul (hM u hu') (norm_riemannThetaTerm_le 0 0 hY
      (fun i => (abs_im_apply_le_norm _ i).trans (hS u hu')) n) (norm_nonneg _)
      ((norm_nonneg _).trans (hM u hu'))
  · have := h.integral_cexp_quadratic (w - fun i => (y i : ℂ))
    rw [mul_assoc (siegelGaussIntegral σ), ← Complex.exp_add]
    convert this using 3 with x
    · rw [hf, ← Complex.exp_add, dotProduct_sub]
      congr 1
      ring
    · rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, neg_mulVec, dotProduct_neg,
        dotProduct_mulVec_comm_of_isSymm hsi w fun i => (y i : ℂ)]
      ring
  · have := (h.neg_inv.summable_norm_riemannThetaTerm 0 0 (σ⁻¹ *ᵥ w)).mul_left
      ‖siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w)))‖
    simpa only [← norm_mul, riemannThetaTerm_zero_zero, ofReal_intCast] using this

theorem IsSiegel.riemannTheta_char_eq_neg_inv {τ : Matrix ι ι ℂ} (h : IsSiegel τ) (a b : ι → ℝ)
    (z : ι → ℂ) :
    riemannTheta b (-a) τ z = siegelGaussIntegral τ * cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) -
      2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (b i : ℂ))) *
      riemannTheta a b (-τ⁻¹) (τ⁻¹ *ᵥ z) := by
  have hsi : τ⁻¹.IsSymm := by rw [Matrix.IsSymm, transpose_nonsing_inv, h.isSymm.eq]
  have e1 := riemannTheta_add_ofReal b 0 (-a) τ z
  have e2 : (z + fun i => ((-a) i : ℂ)) = z - fun i => (a i : ℂ) := by
    ext i
    simp [sub_eq_add_neg]
  have e3 : τ⁻¹ *ᵥ (z - fun i => (a i : ℂ)) = τ⁻¹ *ᵥ z + -τ⁻¹ *ᵥ fun i => (a i : ℂ) := by
    rw [mulVec_sub, neg_mulVec, sub_eq_add_neg]
  have e4 : (fun i => (τ⁻¹ *ᵥ z) i + (b i : ℂ)) = τ⁻¹ *ᵥ z + fun i => (b i : ℂ) := rfl
  rw [zero_add, e2] at e1
  rw [← e1, h.riemannTheta_eq_neg_inv, e3, riemannTheta_add_mulVec_ofReal hsi.neg, zero_add,
    ← mul_assoc, mul_assoc (siegelGaussIntegral τ), ← Complex.exp_add, e4]
  congr 3
  simp only [dotProduct_add, sub_dotProduct, neg_mulVec, dotProduct_neg,
    dotProduct_mulVec_comm_of_isSymm hsi z fun i => (a i : ℂ)]
  ring

end GlobalTheory
