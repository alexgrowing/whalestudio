import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeIcoMeas

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

theorem unfold_Zn {d : ℕ} (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' n : Fin d → ℤ, ∫⁻ x in cubeIco (Fin d), g (x + fun i => (n i : ℝ)) := by
  classical
  set b := Pi.basisFun ℝ (Fin d) with hb
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (Fin d → ℝ) volume :=
    ⟨fun c s _ => by
      show volume ((fun x => (c : Fin d → ℝ) + x) ⁻¹' s) = volume s
      exact measure_preimage_add _ _ _⟩
  have hF := ZSpan.isAddFundamentalDomain b (volume : Measure (Fin d → ℝ))
  have hdom : ZSpan.fundamentalDomain b = cubeIco (Fin d) := by
    ext x; simp [ZSpan.fundamentalDomain, cubeIco, b]
  rw [hF.lintegral_eq_tsum'', hdom]
  have hmem : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Submodule.span ℤ (Set.range b) := by
    intro n
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i; simp [b]
  let e : (Fin d → ℤ) → Submodule.span ℤ (Set.range b) := fun n => ⟨_, hmem n⟩
  have he : Function.Bijective e := by
    constructor
    · intro n m h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      have h2 : (n i : ℝ) = m i := by simpa [e] using this
      exact_mod_cast h2
    · rintro ⟨y, hy⟩
      have hy' := hy
      rw [Module.Basis.mem_span_iff_repr_mem] at hy'
      choose n hn using hy'
      refine ⟨n, Subtype.ext ?_⟩
      funext i
      simpa [b, e] using hn i
  rw [← (Equiv.ofBijective e he).tsum_eq]
  congr 1; funext n
  congr 1; funext x
  show g ((fun i => (n i : ℝ)) + x) = _
  rw [add_comm]

theorem gauss_lin {d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (ob : OrthonormalBasis (Fin d) ℝ W) (u b : Fin d → W)
    (hub : ∀ j i, inner ℝ (u j) (b i) = if j = i then (1 : ℝ) else 0) :
    ∫⁻ a : Fin d → ℝ, ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2)) =
      ENNReal.ofReal (|ob.toBasis.det b| * (2 : ℝ) ^ (-(d : ℝ) / 2)) := by
  classical
  set M : Matrix (Fin d) (Fin d) ℝ := fun i j => ob.repr (u j) i with hM
  set B : Matrix (Fin d) (Fin d) ℝ := ob.toBasis.toMatrix b with hB
  have hMB : M.transpose * B = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hM, hB,
      Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← hub j k, ← ob.sum_inner_mul_inner (u j) (b k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show inner ℝ (ob i) (u j) * _ = _
    rw [real_inner_comm (u j) (ob i)]
  have hdet : M.det * B.det = 1 := by
    have := congrArg Matrix.det hMB
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hdetB : ob.toBasis.det b = B.det := by rw [Module.Basis.det_apply]
  have hM0 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hnorm : ∀ a : Fin d → ℝ,
      ‖∑ j, a j • u j‖ = ‖(WithLp.toLp 2 (M.mulVec a) : EuclideanSpace ℝ (Fin d))‖ := by
    intro a
    rw [← ob.repr.norm_map]
    congr 1
    ext i
    simp [hM, Matrix.mulVec, dotProduct, map_sum, mul_comm]
  set G : (Fin d → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2))
    with hG
  have hGm : Measurable G := by
    refine (Continuous.measurable ?_)
    exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((PiLp.continuous_toLp 2 _).norm.pow 2)))
  have hL : (fun a : Fin d → ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2))) =
      fun a => G (Matrix.toLin' M a) := by
    funext a; simp only [hG, hnorm, Matrix.toLin'_apply]
  rw [hL, ← lintegral_map hGm (Matrix.toLin' M).continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rwa [LinearMap.det_toLin']),
    lintegral_smul_measure, LinearMap.det_toLin']
  have hE : ∫⁻ y, G y =
      ∫⁻ v : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    have hp := MeasurePreserving.symm _
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))
    exact hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun v : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)))
  have hI : ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), finrank_euclideanSpace,
      Fintype.card_fin]
    have h2 : Real.pi / (2 * Real.pi) = (2 : ℝ)⁻¹ := by field_simp
    rw [h2, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_div]
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hI]; positivity
  rw [hE, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), hI, smul_eq_mul,
    ← ENNReal.ofReal_mul (abs_nonneg _), hdetB, eq_inv_of_mul_eq_one_right hdet]

end

end ReciprocityTheory.ChartRestriction.G.I2
