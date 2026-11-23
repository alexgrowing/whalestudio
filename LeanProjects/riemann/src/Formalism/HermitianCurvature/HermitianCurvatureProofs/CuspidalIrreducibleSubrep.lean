import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

noncomputable def geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j ∈ Finset.range n, t ^ (n - 1 - j) • (-X) ^ j

theorem geom {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * geoS X t = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hnil : ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro h; rw [h] at hij; omega
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + k
      · rw [ih i l hl, zero_mul]
      · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]
  have hXn : X ^ n = 0 := by
    ext i j
    have hj := j.isLt
    simp [hnil n i j (by omega)]
  have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
  have h := hc.mul_geom_sum₂ n
  have hS : ∑ i ∈ Finset.range n, (-X) ^ i * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - i) = geoS X t := by
    unfold geoS
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one]
  rw [hS, smul_pow, one_pow, neg_pow, hXn, mul_zero, zero_sub] at h
  have e : t • (1 : Matrix (Fin n) (Fin n) ℂ) + X = -(-X - t • 1) := by rw [neg_sub, sub_neg_eq_add]
  rw [e, neg_mul, h, neg_neg]

theorem det_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hX _ _ le_rfl]
  · intro i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp [Matrix.one_apply_ne hne, hX i j hij.le]

theorem sum_eq_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (t : ℂ) :
    ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold geoS
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      ρ ⬝ᵥ ((∑ j ∈ Finset.range m, t ^ (n - 1 - j) • (-X) ^ j) *ᵥ B) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Matrix.add_mulVec, dotProduct_add,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm (t ^ (n - 1 - k))]
  exact key n

theorem Mcoord_eq {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Mcoord t X B ρ σ = blk (wMat n) 0 0 1 * blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold Mcoord blk
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply]

theorem det_blk_ne {n : ℕ} (t : ℂ) (ht : t ≠ 0) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have hdet : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := det_shift X hX t
  have ht' : t ^ n ≠ 0 := pow_ne_zero n ht
  have hinv : IsUnit (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det := by rw [hdet]; exact ht'.isUnit
  letI := (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).invertibleOfIsUnitDet hinv
  have hA : ⅟(t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) = (t ^ n)⁻¹ • geoS X t := by
    apply invOf_eq_right_inv
    rw [Matrix.mul_smul, geom X hX t, smul_smul, inv_mul_cancel₀ ht', one_smul]
  rw [Matrix.det_fromBlocks₁₁, hdet, hA, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  field_simp
  try ring

theorem continuous_blk_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Continuous fun t : ℂ => blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold blk
  fun_prop

theorem continuous_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Continuous fun t : ℂ => geoS X t := by
  unfold geoS
  fun_prop

theorem det_blk {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  by_cases ht : t = 0
  swap
  · exact det_blk_ne t ht X hX B ρ σ
  have hc1 : Continuous fun s : ℂ => (blk (s • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det :=
    (continuous_blk_shift X B ρ σ).matrix_det
  have hc2 : Continuous fun s : ℂ => s ^ n * σ - ρ ⬝ᵥ (geoS X s *ᵥ B) :=
    ((continuous_pow n).mul continuous_const).sub
      (continuous_const.dotProduct ((continuous_geoS X).matrix_mulVec continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc1 hc2 (fun s hs => det_blk_ne s hs X hX B ρ σ)
  exact congrFun heq t

theorem det_Mcoord {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (Mcoord t X B ρ σ).det = (wMat n).det *
      (t ^ n * σ - ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j)) := by
  have hW : (blk (wMat n) 0 0 1).det = (wMat n).det := by
    unfold blk
    rw [Matrix.det_reindex_self]
    simp only [Pi.zero_apply]
    rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix _ (Fin n) ℂ) = 0 from rfl, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [Mcoord_eq, Matrix.det_mul, det_blk t X hX, sum_eq_geoS, hW]

theorem detMXY : DetMXY := by
  intro m D t p hC
  have hX := isStrictUpper_strictUpper (redOf m p).2.2.1
  have h := det_Mcoord t (strictUpper (redOf m p).2.2.1) hX (redOf m p).2.2.2
    (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1
  rw [cornerSplit m _ _ _ _ t] at h
  have e : detM (MXY m D t p) = (Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
      (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1).det := rfl
  rw [e, h]
  congr 1
  have hC' : Cof (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t ≠ 0 := hC
  rw [rhoXY, rho1, mul_div_cancel₀ _ hC']
  ring

theorem redIntegrable : RedIntegrable := by
  intro m β t c ht V _ _ _ Φ hint
  have hemb := embedding_coordMap (m + 1) t ht
  have hJ := jacobian (m + 1) β t ht
  have hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t :=
    funext (blockIntegrand_eq β m Φ t c ht)
  have hpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  have hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1)) := by
    have h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) :=
      hemb.integrable_map_iff.2 (hfun ▸ hint)
    rw [hJ, ENNReal.smul_def] at h
    exact (integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h
  have hmp := mp_consMap β m
  have hG : Integrable (fun q => Fint β m Φ t c (consMap m q)) (muRed β m) :=
    hmp.integrable_comp_of_integrable hF
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  set α : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t with hα
  set γ : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t with hγ
  have hαm : Measurable α := measurable_const.div hcC
  have hγm : Measurable γ := (measurable_const.sub (continuous_remainder m t).measurable).div hcC
  have hm := affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    α γ hαm hγm ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
  have hT : Measurable (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m)) := by fun_prop
  have hd : Measurable (fun p : RedCoord m => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hG' : Integrable (fun q => Fint β m Φ t c (consMap m q))
      (Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)))) := by
    have : Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = muRed β m := hm
    rw [this]; exact hG
  have h5 := hG'.comp_measurable hT
  have h6 := (integrable_withDensity_iff_integrable_smul hd).1 h5
  have h7 : Integrable (fun q : RedCoord m => ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      redIntegrand β m Φ (c * t ^ (m + 1)) t q) (muRed β m) := by
    refine h6.congr (Filter.Eventually.of_forall fun q => ?_)
    have := pointwise_red β m Φ t c ht q
    simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Function.comp]
    rw [← Complex.coe_smul]
    exact this
  have hne : ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  exact (integrable_smul_iff hne _).1 h7

theorem innerXYOfReduced : InnerXYOfReduced := by
  intro hOm hRI hSplit hAmp m β t c ht V _ _ _ Φ hint
  have hmp := (hSplit m β).2
  have i1 : PolishSpace (XY m) := inferInstance
  have i2 : StandardBorelSpace (XY m) := inferInstance
  have i3 : SecondCountableTopology (RedCoord m) := inferInstance
  have i4 : MeasurableSpace.CountablyGenerated (RedCoord m) := inferInstance
  have i5 : MeasurableSpace.CountablySeparated (RedCoord m) := inferInstance
  have hemb : MeasurableEmbedding (redOf m) := hmp.measurable.measurableEmbedding (hSplit m β).1.injective
  have hfun : (fun p : XY m =>
      psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p) =
      redIntegrand β m Φ (c * t ^ (m + 1)) t ∘ redOf m :=
    funext fun p => hAmp m β (c * t ^ (m + 1)) t ht V Φ p
  have h1 := hRI m β t c ht V Φ hint
  have h2 := hOm m β t c ht V Φ hint
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hmp.integrable_comp_emb hemb).2 h1
  · rw [h2, hfun]
    exact (hmp.integral_comp hemb _).symm

end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

namespace Formalism.FourierDecayAlt.P

theorem det_matrix_xy : Formalism.FourierDecayAlt.G.DetMXY := CuspidalIrreducibleSubrep.detMXY

theorem reduced_integrand_integrable : Formalism.FourierDecayAlt.G.RedIntegrable := CuspidalIrreducibleSubrep.redIntegrable

theorem inner_xy_of_reduced : Formalism.FourierDecayAlt.G.InnerXYOfReduced := CuspidalIrreducibleSubrep.innerXYOfReduced

end Formalism.FourierDecayAlt.P
