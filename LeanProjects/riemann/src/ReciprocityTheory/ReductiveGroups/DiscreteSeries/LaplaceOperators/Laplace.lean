import Mathlib

open MeasureTheory Complex Filter Topology Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace

theorem gauss_diag {d : ℕ} (b : Fin d → ℂ) (hb : ∀ i, 0 < (b i).re) :
    ∫ v : Fin d → ℝ, cexp (-∑ i, b i * (v i : ℂ) ^ 2) ≠ 0 := by
  have hb0 : ∀ i, b i ≠ 0 := fun i h => by
    have h' := hb i
    rw [h] at h'
    simp at h'
  have h := GaussianFourier.integral_cexp_neg_sum_mul_add hb (fun _ => (0 : ℂ))
  simp only [zero_mul, Finset.sum_const_zero, add_zero] at h
  rw [h, Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]
  rintro ⟨h1, -⟩
  exact div_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) (hb0 i) h1

open scoped MatrixOrder in
theorem simdiag {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, IsUnit P ∧ ∃ c : Fin d → ℝ,
      Pᵀ * A * P = 1 ∧ Pᵀ * C * P = diagonal c := by
  have spec : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian),
      ∃ U : Matrix (Fin d) (Fin d) ℝ, Uᵀ * U = 1 ∧ Uᵀ * M * U = diagonal hM.eigenvalues := by
    intro M hM
    have hst : star (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) =
        (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have h1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
    have h2 := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at h2
    rw [hst] at h1 h2
    obtain ⟨U, hU1, hU2⟩ : ∃ U : Matrix (Fin d) (Fin d) ℝ,
        Uᵀ * U = 1 ∧ M = U * diagonal hM.eigenvalues * Uᵀ := ⟨_, h1, h2⟩
    refine ⟨U, hU1, ?_⟩
    calc Uᵀ * M * U = Uᵀ * (U * diagonal hM.eigenvalues * Uᵀ) * U :=
          congrArg (fun X => Uᵀ * X * U) hU2
      _ = (Uᵀ * U) * diagonal hM.eigenvalues * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = diagonal hM.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hCt : Cᵀ = C := by
    have h := hC
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨U, hU1, hU2⟩ := spec A hA.1
  obtain ⟨s, hs⟩ : ∃ s : Fin d → ℝ, ∀ i, s i * hA.1.eigenvalues i * s i = 1 := by
    refine ⟨fun i => (Real.sqrt (hA.1.eigenvalues i))⁻¹, fun i => ?_⟩
    have h0 := hA.eigenvalues_pos i
    rw [show (Real.sqrt (hA.1.eigenvalues i))⁻¹ * hA.1.eigenvalues i *
        (Real.sqrt (hA.1.eigenvalues i))⁻¹ =
        hA.1.eigenvalues i / (Real.sqrt (hA.1.eigenvalues i) * Real.sqrt (hA.1.eigenvalues i)) by ring,
      Real.mul_self_sqrt h0.le, div_self h0.ne']
  have hQ' : (U * diagonal s)ᵀ * A * (U * diagonal s) = 1 := by
    have e1 : (U * diagonal s)ᵀ * A * (U * diagonal s) = diagonal s * (Uᵀ * A * U) * diagonal s := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hU2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hs i
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin d) (Fin d) ℝ, Qᵀ * A * Q = 1 := ⟨_, hQ'⟩
  have hC' : (Qᵀ * C * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hCt, Matrix.mul_assoc]
  obtain ⟨V, hV1, hV2⟩ := spec _ hC'
  have hPA : (Q * V)ᵀ * A * (Q * V) = 1 := by
    have e : (Q * V)ᵀ * A * (Q * V) = Vᵀ * (Qᵀ * A * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hQ, Matrix.mul_one, hV1]
  have hPC : (Q * V)ᵀ * C * (Q * V) = diagonal hC'.eigenvalues := by
    have e : (Q * V)ᵀ * C * (Q * V) = Vᵀ * (Qᵀ * C * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hV2]
  have hdet := congrArg Matrix.det hPA
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hP : IsUnit (Q * V) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_mul]
    intro h0
    rw [h0] at hdet
    simp at hdet
  exact ⟨Q * V, hP, hC'.eigenvalues, hPA, hPC⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    ∃ (L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) (b : Fin (Module.finrank ℝ E) → ℂ),
      (∀ i, 0 < (b i).re) ∧ ∀ w, B (L w) (L w) = ∑ i, b i * (w i : ℂ) ^ 2 := by
  let e := Module.finBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
  let C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
  have hexp : ∀ x : Fin (Module.finrank ℝ E) → ℝ, B (e.equivFun.symm x) (e.equivFun.symm x) =
      ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (e i) (e j) := by
    intro x
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Complex.real_smul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hsymm : ∀ (x : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j = ∑ i, ∑ j, x i * x j * f i j := by
    intro x f
    have h1 : ∑ i, ∑ j, x i * x j * f j i = ∑ i, ∑ j, x i * x j * f i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j =
        (∑ i, ∑ j, x i * x j * f i j + ∑ i, ∑ j, x i * x j * f j i) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, h1]
    ring
  have hre : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).re = x ⬝ᵥ (A *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).re), hexp]
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have him : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).im = x ⬝ᵥ (C *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).im), hexp]
    simp only [Complex.im_sum, Complex.im_ofReal_mul]
  have hAh : A.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).re + (B (e i) (e j)).re) / 2) =
      ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
    rw [star_trivial, add_comm]
  have hCh : C.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).im + (B (e i) (e j)).im) / 2) =
      ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
    rw [star_trivial, add_comm]
  have hApd : A.PosDef := by
    refine ⟨hAh, fun x hx => ?_⟩
    have key : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) = (⇑x) ⬝ᵥ (A *ᵥ ⇑x) := by
      rw [Finsupp.sum_fintype]
      · show ∑ i, (x.sum fun j xj => star (x i) * A i j * xj) = ∑ i, x i * ∑ j, A i j * x j
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.sum_fintype]
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [star_trivial]; ring
        · intro j; simp
      · intro i; simp
    rw [key, ← hre]
    refine hB _ ((LinearEquiv.map_ne_zero_iff _).2 ?_)
    intro h0
    exact hx (Finsupp.ext fun i => by simpa using congrFun h0 i)
  obtain ⟨P, hP, c, hPA, hPC⟩ := simdiag A C hApd hCh
  have hcong : ∀ (M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (w : Fin (Module.finrank ℝ E) → ℝ),
      (P *ᵥ w) ⬝ᵥ (M *ᵥ (P *ᵥ w)) = w ⬝ᵥ ((Pᵀ * M * P) *ᵥ w) := by
    intro M w
    rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose P w, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨(Matrix.toLinearEquiv' P hP.invertible).trans e.equivFun.symm,
    fun i => 1 + (c i : ℂ) * I, fun i => by simp, fun w => ?_⟩
  have hd : diagonal c *ᵥ w = fun i => c i * w i := funext (Matrix.mulVec_diagonal c w)
  show B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w)) = _
  rw [← Complex.re_add_im (B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w))), hre, him,
    hcong, hcong, hPA, hPC, Matrix.one_mulVec, hd]
  show ((∑ i, w i * w i : ℝ) : ℂ) + ((∑ i, w i * (c i * w i) : ℝ) : ℂ) * I = _
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem gauss_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) : ∫ v, cexp (-(B v v)) ∂μ ≠ 0 := by
  obtain ⟨L, b, hb, hL⟩ := exists_diag B hB
  have hemb : MeasurableEmbedding
      (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) :=
    L.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hμ : μ = Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) •
      Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume := by
    apply Measure.isAddLeftInvariant_eq_smul
  have hc : 0 < Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) := by
    apply Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
  have h2 : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      cexp (-(B (L.toContinuousLinearEquiv w) (L.toContinuousLinearEquiv w))) =
        cexp (-∑ i, b i * (w i : ℂ) ^ 2) := by
    intro w
    rw [show L.toContinuousLinearEquiv w = L w from rfl, hL]
  rw [hμ, integral_smul_nnreal_measure, hemb.integral_map]
  simp_rw [h2]
  rw [NNReal.smul_def, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (NNReal.coe_pos.2 hc).ne') (gauss_diag b hb)

theorem mono_pow {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) :
    (1 + x / s) ^ s ≤ (1 + x / t) ^ t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hp0 : 0 ≤ s / t := div_nonneg hs.le ht.le
  have hp1 : s / t ≤ 1 := (div_le_one ht).2 hst
  have hb : 0 ≤ 1 + x / s := add_nonneg zero_le_one (div_nonneg hx hs.le)
  have key : (1 + x / s) ^ (s / t) ≤ 1 + x / t := by
    have h := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1) hb zero_le_one
      (by ring : s / t + (1 - s / t) = 1)
    rw [Real.one_rpow, mul_one] at h
    calc (1 + x / s) ^ (s / t) ≤ s / t * (1 + x / s) + (1 - s / t) * 1 := h
      _ = 1 + x / t := by field_simp <;> ring
  calc (1 + x / s) ^ s = ((1 + x / s) ^ (s / t)) ^ t := by
        rw [← Real.rpow_mul hb]
        congr 1
        field_simp
    _ ≤ (1 + x / t) ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hb _) key ht.le

end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
