import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RSubMean

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex Metric

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  first
  | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
  | rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace]
  | (rw [(WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq, Module.finrank_pi_fintype]
     simp [Complex.finrank_real_complex, mul_comm])
  | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]

theorem lemS_local (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F)
    (v0 : EuclideanSpace ℂ ι) :
    ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) ≤
      2 * (q : ℝ) ^ Fintype.card ι *
        ∫ u in closedBall v0 (Real.sqrt (2 * Fintype.card ι) / Real.sqrt (q * Real.pi)),
          ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
  set s := Real.sqrt (q * Real.pi) with hs
  set ρ := Real.sqrt (2 * Fintype.card ι) with hρ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q * Real.pi := mul_pos (by linarith) Real.pi_pos
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt hqpos.le
  let eC : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  let eR : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (Fintype.equivFin ι)
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin (Fintype.card ι)) → EuclideanSpace ℂ ι,
      w = fun z => s⁻¹ • eC.symm z := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℂ (Fin (Fintype.card ι)) → ℂ,
      G = fun z => F (v0 + w z) * Complex.exp (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)) :=
    ⟨_, rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ Hf : EuclideanSpace ℂ ι → ℝ,
      Hf = fun u => ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := ⟨_, rfl⟩
  have hwd : Differentiable ℂ w := by
    rw [hw]
    exact (eC.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiable).const_smul s⁻¹
  have hGd : Differentiable ℂ G := by
    rw [hG]
    refine (hF.comp ((differentiable_const v0).add hwd)).mul ?_
    refine Differentiable.cexp ?_
    refine (differentiable_const _).mul ?_
    exact (innerSL ℂ v0).differentiable.comp hwd
  have hwn : ∀ z, ‖w z‖ = s⁻¹ * ‖z‖ := by
    intro z
    rw [hw]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hw0 : w 0 = 0 := by rw [hw]; simp
  have hexp2 : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have key : ∀ z, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Hf (v0 + w z) := by
    intro z
    have hz : ‖z‖ ^ 2 = q * Real.pi * ‖w z‖ ^ 2 := by
      rw [hwn, mul_pow, ← hs2, inv_pow]
      field_simp
    have hadd : ‖v0 + w z‖ ^ 2 = ‖v0‖ ^ 2 + 2 * (inner ℂ v0 (w z)).re + ‖w z‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ)]
      first | rfl | simp
    have hre : (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)).re =
        -(q * Real.pi) * (inner ℂ v0 (w z)).re := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have e1 : Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2) =
        Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0 + w z‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, hz, hadd]
      congr 1
      ring
    calc ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ‖F (v0 + w z)‖ ^ 2 *
            (Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2)) := by
          rw [hG]
          simp only [norm_mul, Complex.norm_exp, mul_pow, hre, hexp2]
          ring
      _ = _ := by rw [e1, hHf]; ring
  have hmem : ∀ z, v0 + w z ∈ Metric.closedBall v0 (ρ / s) ↔
      z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ := by
    intro z
    have hsub : v0 + w z - v0 = w z := by abel
    rw [Metric.mem_closedBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, hsub, sub_zero, hwn,
      div_eq_inv_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h (inv_pos.mpr hs0),
      fun h => mul_le_mul_of_nonneg_left h (inv_pos.mpr hs0).le⟩
  have hA : ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
      ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_const_mul]
    congr 1
    funext z
    by_cases hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ
    · rw [Set.indicator_of_mem hzb, Set.indicator_of_mem ((hmem z).2 hzb), key z]
    · have h2 : v0 + w z ∉ Metric.closedBall v0 (ρ / s) := fun h => hzb ((hmem z).1 h)
      simp [Set.indicator_apply, hzb, h2]
  have hC : ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) =
      s ^ (2 * Fintype.card ι) * ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u := by
    set h := (Metric.closedBall v0 (ρ / s)).indicator Hf
    have h1 : ∫ z, h (v0 + w z) = ∫ y, h (v0 + s⁻¹ • y) := by
      rw [hw]
      exact (eR.symm.measurePreserving).integral_comp eR.symm.toHomeomorph.measurableEmbedding
        (fun y => h (v0 + s⁻¹ • y))
    rw [h1, MeasureTheory.Measure.integral_comp_smul (μ := volume) (fun y => h (v0 + y)) s⁻¹,
      lemS_finrank, integral_add_left_eq_self, inv_pow, inv_inv, abs_of_pos (pow_pos hs0 _),
      smul_eq_mul]
  have L : ‖G 0‖ ^ 2 ≤ 2 / Real.pi ^ Fintype.card ι *
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
        ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := sq_norm_zero_le_gauss_ball G hGd
  have hG0 : G 0 = F v0 := by rw [hG]; simp [hw0]
  have hsn : s ^ (2 * Fintype.card ι) = (q * Real.pi) ^ Fintype.card ι := by rw [pow_mul, hs2]
  have hJ : ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u =
      ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
    rw [integral_indicator measurableSet_closedBall, hHf]
  rw [hA, hC, hG0, hsn, hJ] at L
  have hE : Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hpi : Real.pi ^ Fintype.card ι ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  set J := ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)
  calc ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)
      ≤ 2 / Real.pi ^ Fintype.card ι *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ((q * Real.pi) ^ Fintype.card ι * J)) *
          Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) := mul_le_mul_of_nonneg_right L (Real.exp_pos _).le
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J * (Real.pi ^ Fintype.card ι / Real.pi ^ Fintype.card ι) *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)) := by
        rw [mul_pow]; ring
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J := by rw [hE, div_self hpi]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
