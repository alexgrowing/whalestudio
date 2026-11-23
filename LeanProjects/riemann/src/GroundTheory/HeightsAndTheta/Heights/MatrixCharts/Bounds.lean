import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix
open scoped ComplexOrder

noncomputable section

variable (D : PeriodChartData)

theorem cusp_norm_lt {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    ‖cuspCoord D.a_le z j‖ < 1 :=
  D.U_subset hz (Fin.castLE D.a_le j)

theorem log_inv_sq_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by
  rw [Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg w) hw.le))

theorem exp_one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : Real.exp 1 ≤ D.radius z := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => log_inv_sq_nonneg (cusp_norm_lt D hz j)
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ D.radius z := by
  have := exp_one_le_radius D hz
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem one_le_log_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ Real.log (D.radius z) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (exp_one_le_radius D hz)

theorem cuspTime_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    cuspTime D.a_le z j ≤ D.radius z := by
  have hlt := cusp_norm_lt D hz j
  have hL : 0 ≤ -Real.log ‖cuspCoord D.a_le z j‖ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hlt.le)
  have hterm : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ = 2 * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hsum : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ ≤
      ∑ i, Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ :=
    Finset.single_le_sum (f := fun i => Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹)
      (fun i _ => log_inv_sq_nonneg (cusp_norm_lt D hz i)) (Finset.mem_univ j)
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have he := Real.exp_pos 1
  have h1 : cuspTime D.a_le z j = (2 * Real.pi)⁻¹ * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [cuspTime, Real.log_inv]
  have h2 := mul_le_mul_of_nonneg_right hpi hL
  rw [h1]
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem Y_transpose {z : Fin D.n → ℂ} (hz : z ∈ D.U) : (D.Y z)ᵀ = D.Y z := by
  ext j k
  simp only [transpose_apply, PeriodChartData.Y, chartImag, Matrix.add_apply, map_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show D.τ0 z k j = D.τ0 z j k from by simpa using congrFun (congrFun (D.τ0_symm z hz) j) k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show D.B i k j = D.B i j k from by simpa using (D.B_psd i).isHermitian.apply j k]

theorem exists_bound_imτ0 : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ D.K, entrySum ((D.τ0 p.1).map Complex.im) ≤ M := by
  have hcont : ContinuousOn (fun z => entrySum ((D.τ0 z).map Complex.im)) D.U := by
    unfold entrySum
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    simp only [map_apply]
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn (D.τ0_analytic j k).continuousOn)
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hM p.1 ⟨p, hp, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

theorem quad_Y_le {z : Fin D.n → ℂ} (hz : z ∈ D.U) (M : ℝ)
    (hM : entrySum ((D.τ0 z).map Complex.im) ≤ M) (x : Fin D.g → ℝ) :
    x ⬝ᵥ (D.Y z *ᵥ x) ≤ (M + ∑ j, entrySum (D.B j)) * D.radius z * (x ⬝ᵥ x) := by
  have hr1 := one_le_radius D hz
  have hxx := dot_self_nonneg x
  have hM0 : 0 ≤ M := (entrySum_nonneg _).trans hM
  simp only [PeriodChartData.Y, chartImag]
  rw [add_mulVec, dotProduct_add, quad_sum]
  have h0 : x ⬝ᵥ ((D.τ0 z).map Complex.im *ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
    have h3 := (le_abs_self _).trans (abs_quad_le ((D.τ0 z).map Complex.im) x)
    have h2 : entrySum ((D.τ0 z).map Complex.im) * (x ⬝ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
      apply mul_le_mul_of_nonneg_right _ hxx
      nlinarith
    linarith
  have h1 : ∀ j, x ⬝ᵥ ((cuspTime D.a_le z j • D.B j) *ᵥ x) ≤
      entrySum (D.B j) * D.radius z * (x ⬝ᵥ x) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have ht1 := cuspTime_le_radius D hz j
    have hq := (le_abs_self _).trans (abs_quad_le (D.B j) x)
    have hq0 := quad_nonneg (D.B_psd j) x
    have hr0 : 0 ≤ D.radius z := by linarith
    calc cuspTime D.a_le z j * (x ⬝ᵥ (D.B j *ᵥ x)) ≤ D.radius z * (entrySum (D.B j) * (x ⬝ᵥ x)) :=
          mul_le_mul ht1 hq hq0 hr0
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h1 j
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  linarith

theorem exists_Y_le : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K,
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_imτ0 D
  have hβ : 0 ≤ ∑ j, entrySum (D.B j) := Finset.sum_nonneg fun j _ => entrySum_nonneg _
  refine ⟨M + ∑ j, entrySum (D.B j) + 1, by positivity, fun p hp => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 := one_le_radius D hz
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, Y_transpose D hz]
  · rw [quad_smul_one_sub]
    have h := quad_Y_le D hz M (hM p hp) x
    have hxx := dot_self_nonneg x
    nlinarith

theorem injective_of_rank {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin F)
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank ℂ (LinearMap.ker F.mulVecLin) = 0 := by
    unfold Matrix.rank at h; omega
  have h3 : LinearMap.ker F.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h2
  exact LinearMap.ker_eq_bot.mp h3

theorem gram_posDef {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef :=
  PosDef.conjTranspose_mul_self F (injective_of_rank F h)

theorem continuousOn_f : ContinuousOn D.f (D.U ×ˢ D.V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_matrix fun j k => (D.f_analytic j k).continuousOn.domRestrict

theorem exists_gram_bounds : ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ p ∈ D.K,
    δ ≤ ((D.f p)ᴴ * D.f p).det.re ∧ ((D.f p)ᴴ * D.f p).det.re ≤ M := by
  have hc : ContinuousOn (fun p => ((D.f p)ᴴ * D.f p).det.re) D.K := by
    have h := (continuousOn_f D).mono D.K_subset
    rw [continuousOn_iff_continuous_domRestrict] at h ⊢
    exact Complex.continuous_re.comp (h.matrix_conjTranspose.matrix_mul h).matrix_det
  have hpos : ∀ p ∈ D.K, 0 < ((D.f p)ᴴ * D.f p).det.re := fun p hp =>
    MCDet.re_det_pos (gram_posDef _ (D.f_rank p (D.K_subset hp)))
  rcases D.K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, 1, one_pos, one_pos, fun p hp => by simp [hK] at hp⟩
  obtain ⟨p0, hp0, hmin⟩ := D.isCompact_K.exists_isMinOn hK hc
  obtain ⟨M, hM⟩ := D.isCompact_K.exists_bound_of_continuousOn hc
  refine ⟨_, max M 1, hpos p0 hp0, by positivity, fun p hp => ⟨hmin hp, ?_⟩⟩
  have h := hM p hp
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

end

end GroundTheory.Heights₂.Heights.MCBounds
