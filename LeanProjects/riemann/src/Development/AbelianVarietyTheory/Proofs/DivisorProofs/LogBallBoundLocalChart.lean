import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInverseQuantitativeBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNegLogBallBoundStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LogModel

open Metric

theorem cov_le {d : ℕ} (s : Set (ReciprocityTheory.L2DbarEstimates.V d)) (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (J : ℝ)
    (g : ReciprocityTheory.L2DbarEstimates.V d → ENNReal) (hs : MeasurableSet s) (hinj : Set.InjOn Ψ s)
    (hd : ∀ x ∈ s, HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) s x) (hJ : 0 < J)
    (hdet : ∀ x ∈ s, J ≤ |(fderiv ℝ Ψ x).det|) :
    ∫⁻ x in s, g (Ψ x) ≤ ENNReal.ofReal J⁻¹ * ∫⁻ y in Ψ '' s, g y := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd hinj]
  calc ∫⁻ x in s, g (Ψ x) = ∫⁻ x in s, ENNReal.ofReal J⁻¹ * (ENNReal.ofReal J * g (Ψ x)) := by
        refine lintegral_congr fun x => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hJ.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal J⁻¹ * ∫⁻ x in s, ENNReal.ofReal J * g (Ψ x) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' hs fun x hx => ?_)
        gcongr
        exact hdet x hx

theorem vol_coord_zero {d : ℕ} (i : Fin d) : volume {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0} = 0 := by
  let φ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ℂ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℂ) i
  have h : {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0} = (LinearMap.ker (φ : ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ℂ) : Set _) := by
    ext w; simp [φ]
  rw [h]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : EuclideanSpace.single i (1 : ℂ) ∈ LinearMap.ker (φ : ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ℂ) := htop ▸ Submodule.mem_top
  simp [φ] at this

theorem image_ball_sub {d : ℕ} (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (s : Set (ReciprocityTheory.L2DbarEstimates.V d)) (L : ℝ)
    (x : ReciprocityTheory.L2DbarEstimates.V d) (ρ : ℝ) (hL : 0 ≤ L) (hs : ball x ρ ⊆ s)
    (hd : ∀ v ∈ s, HasFDerivAt Ψ (fderiv ℝ Ψ v) v) (hn : ∀ v ∈ s, ‖fderiv ℝ Ψ v‖ ≤ L) :
    Ψ '' ball x ρ ⊆ ball (Ψ x) ((L + 1) * ρ) := by
  rintro _ ⟨y, hy, rfl⟩
  have hρ : 0 < ρ := pos_of_mem_ball hy
  have h := (convex_ball x ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v hv => (hd v (hs hv)).hasFDerivWithinAt) (fun v hv => hn v (hs hv)) (mem_ball_self hρ) hy
  rw [mem_ball, dist_eq_norm]
  have hy' : ‖y - x‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hy
  calc ‖Ψ y - Ψ x‖ ≤ L * ‖y - x‖ := h
    _ ≤ L * ρ := mul_le_mul_of_nonneg_left hy'.le hL
    _ < (L + 1) * ρ := by nlinarith

theorem coord_cont {d : ℕ} (i : Fin d) : Continuous fun w : ReciprocityTheory.L2DbarEstimates.V d => w i := by fun_prop

theorem coord_bound {d : ℕ} (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (S : Set (ReciprocityTheory.L2DbarEstimates.V d)) (J L : ℝ)
    (hJ : 0 < J) (hL : 0 ≤ L) (hinj : Set.InjOn Ψ S) (hd : ∀ v ∈ S, HasFDerivAt Ψ (fderiv ℝ Ψ v) v)
    (hdet : ∀ v ∈ S, J ≤ |(fderiv ℝ Ψ v).det|) (hn : ∀ v ∈ S, ‖fderiv ℝ Ψ v‖ ≤ L) (hc : ContinuousOn Ψ S)
    (i : Fin d) (v : ReciprocityTheory.L2DbarEstimates.V d) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : (L + 1) * ρ ≤ 1) (hsub : ball v ρ ⊆ S) :
    IntegrableOn (fun x => max 0 (-Real.log (‖Ψ x i‖ ^ 2))) (ball v ρ) ∧
      ∫ x in ball v ρ, max 0 (-Real.log (‖Ψ x i‖ ^ 2)) ≤
        J⁻¹ * ((Real.pi * ((L + 1) * ρ) ^ 2) ^ d * (1 - 2 * Real.log (((L + 1) * ρ) ^ 2))) := by
  set B := (Real.pi * ((L + 1) * ρ) ^ 2) ^ d * (1 - 2 * Real.log (((L + 1) * ρ) ^ 2)) with hBdef
  have hr : 0 < (L + 1) * ρ := by positivity
  have hB : 0 ≤ B := by
    have : Real.log (((L + 1) * ρ) ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ hr.le hρ1)
    have : 0 ≤ 1 - 2 * Real.log (((L + 1) * ρ) ^ 2) := by linarith
    positivity
  have hg0 : ∀ x, 0 ≤ max 0 (-Real.log (‖Ψ x i‖ ^ 2)) := fun x => le_max_left _ _
  have hGm : Measurable fun w : ReciprocityTheory.L2DbarEstimates.V d => max 0 (-Real.log (‖w i‖ ^ 2)) := by
    have := (coord_cont i).measurable
    fun_prop
  have hgm : AEMeasurable (fun x => max 0 (-Real.log (‖Ψ x i‖ ^ 2))) (volume.restrict (ball v ρ)) :=
    hGm.comp_aemeasurable ((hc.mono hsub).aemeasurable measurableSet_ball)
  have hlin : ∫⁻ x in ball v ρ, ENNReal.ofReal (max 0 (-Real.log (‖Ψ x i‖ ^ 2))) ≤ ENNReal.ofReal (J⁻¹ * B) := by
    calc _ ≤ ENNReal.ofReal J⁻¹ * ∫⁻ y in Ψ '' ball v ρ, ENNReal.ofReal (max 0 (-Real.log (‖y i‖ ^ 2))) :=
          cov_le (ball v ρ) Ψ J (fun y => ENNReal.ofReal (max 0 (-Real.log (‖y i‖ ^ 2)))) measurableSet_ball
            (hinj.mono hsub) (fun x hx => (hd x (hsub hx)).hasFDerivWithinAt) hJ (fun x hx => hdet x (hsub hx))
      _ ≤ ENNReal.ofReal J⁻¹ * ∫⁻ y in ball (Ψ v) ((L + 1) * ρ), ENNReal.ofReal (max 0 (-Real.log (‖y i‖ ^ 2))) :=
          by gcongr; exact image_ball_sub Ψ S L v ρ hL hsub hd hn
      _ ≤ ENNReal.ofReal J⁻¹ * ENNReal.ofReal B := by gcongr; exact GlobalTheory.T.lintegral_neg_log_ball_bound _ _ i hr hρ1
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hint : IntegrableOn (fun x => max 0 (-Real.log (‖Ψ x i‖ ^ 2))) (ball v ρ) :=
    ⟨hgm.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
      exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (J⁻¹ * B)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = J⁻¹ * B := ENNReal.toReal_ofReal (by positivity)

theorem main : ∀ {d : ℕ} (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (v₀ : ReciprocityTheory.L2DbarEstimates.V d) (Φ : ReciprocityTheory.L2DbarEstimates.V d → (Fin d → ℂ)) (H f : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (I : Finset (Fin d)), IsOpen U → v₀ ∈ U → ContDiffOn ℝ 1 Φ U → Function.Bijective (fderiv ℝ Φ v₀) → ContinuousOn H U → (∀ v, 0 ≤ f v) → (∀ v ∈ U, (∀ i ∈ I, Φ v i ≠ 0) → f v = H v - ∑ i ∈ I, Real.log (‖Φ v i‖ ^ 2)) → GlobalTheory.LogMean.LogBallBd f v₀ (2 * d) := by
  intro d U v₀ Φ H f I hU hv₀ hΦ hbij hH hf0 hf
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)
  let Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d := fun v => e.symm (Φ v)
  have hΨi : ∀ v i, Ψ v i = Φ v i := fun v i => by simp [Ψ, e]
  have hΨ : ContDiffOn ℝ 1 Ψ U := e.symm.contDiff.comp_contDiffOn hΦ
  have hbijΨ : Function.Bijective (fderiv ℝ Ψ v₀) := by
    have : fderiv ℝ Ψ v₀ = (e.symm : (Fin d → ℂ) →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d).comp (fderiv ℝ Φ v₀) :=
      e.symm.comp_fderiv
    rw [this, ContinuousLinearMap.coe_comp']
    exact e.symm.bijective.comp hbij
  obtain ⟨r, J, L, hr, hJ, hL, hrU, hinj, hder⟩ := GlobalTheory.T.local_inverse_quantitative_ball U v₀ Ψ hU hv₀ hΨ hbijΨ
  have hdS : ∀ v ∈ Metric.ball v₀ r, HasFDerivAt Ψ (fderiv ℝ Ψ v) v := fun v hv =>
    ((hΨ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hrU hv))).hasFDerivAt
  have hcS : ContinuousOn Ψ (Metric.ball v₀ r) := hΨ.continuousOn.mono hrU
  have hΨm : AEMeasurable Ψ (volume.restrict (Metric.ball v₀ r)) := hcS.aemeasurable Metric.isOpen_ball.measurableSet

  have hnz : ∀ᵐ x ∂(volume.restrict (Metric.ball v₀ r)), ∀ i, Φ x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have hP : MeasurableSet {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0} :=
      (isClosed_eq (coord_cont i) continuous_const).measurableSet
    have h0 := cov_le (Metric.ball v₀ r) Ψ J ({w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0}.indicator 1)
      Metric.isOpen_ball.measurableSet hinj (fun x hx => (hdS x hx).hasFDerivWithinAt) hJ (fun x hx => (hder x hx).1)
    have h1 : ∫⁻ y in Ψ '' Metric.ball v₀ r, {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0}.indicator 1 y = 0 := by
      refine le_antisymm ?_ bot_le
      calc _ ≤ ∫⁻ y, {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0}.indicator 1 y := setLIntegral_le_lintegral _ _
        _ = volume {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0} := lintegral_indicator_one hP
        _ = 0 := vol_coord_zero i
    rw [h1, mul_zero, nonpos_iff_eq_zero] at h0
    have hm : AEMeasurable (fun x => {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0}.indicator (1 : ReciprocityTheory.L2DbarEstimates.V d → ENNReal) (Ψ x))
        (volume.restrict (Metric.ball v₀ r)) := (measurable_one.indicator hP).comp_aemeasurable hΨm
    rw [lintegral_eq_zero_iff' hm] at h0
    filter_upwards [h0] with x hx hx0
    have hmem : Ψ x ∈ {w : ReciprocityTheory.L2DbarEstimates.V d | w i = 0} := by simp [hΨi, hx0]
    simp [Set.indicator_of_mem hmem] at hx

  set L' := L + 1 with hL'
  have hL'1 : 1 ≤ L' := by linarith
  set δ := min (r / 3) (1 / L') with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ r / 3 := min_le_left _ _
  have hδL : δ ≤ 1 / L' := min_le_right _ _
  have hKS : Metric.closedBall v₀ (2 * δ) ⊆ Metric.ball v₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall v₀ (2 * δ)).exists_bound_of_continuousOn (hH.mono (hKS.trans hrU))
  set c := volume.real (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V d) 1) with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  set A := (Real.pi * L' ^ 2) ^ d with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨δ, max M 0 * c + I.card * (J⁻¹ * A * 4), hδ, by positivity, fun v hv ρ hρ hρδ => ?_⟩
  have hball : Metric.ball v ρ ⊆ Metric.closedBall v₀ (2 * δ) := by
    intro y hy
    rw [Metric.mem_closedBall] at hv ⊢
    rw [Metric.mem_ball] at hy
    linarith [dist_triangle y v v₀]
  have hbS : Metric.ball v ρ ⊆ Metric.ball v₀ r := hball.trans hKS
  have hρ1 : L' * ρ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hρδ.trans hδL) (by linarith : (0:ℝ) ≤ L')
    rwa [mul_one_div_cancel (by linarith)] at this
  have hρle1 : ρ ≤ 1 := by nlinarith
  set ℓ := Real.log (1 / ρ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)

  have hcoord : ∀ i, IntegrableOn (fun x => max 0 (-Real.log (‖Ψ x i‖ ^ 2))) (Metric.ball v ρ) ∧
      ∫ x in Metric.ball v ρ, max 0 (-Real.log (‖Ψ x i‖ ^ 2)) ≤ J⁻¹ * A * 4 * (ρ ^ (2 * d) * (1 + ℓ)) := by
    intro i
    obtain ⟨h1, h2⟩ := coord_bound Ψ (Metric.ball v₀ r) J L hJ hL hinj hdS (fun x hx => (hder x hx).1)
      (fun x hx => (hder x hx).2) hcS i v ρ hρ hρ1 hbS
    refine ⟨h1, h2.trans ?_⟩
    have hlog : Real.log ((L' * ρ) ^ 2) = 2 * Real.log L' - 2 * ℓ := by
      rw [Real.log_pow, Real.log_mul (by positivity) hρ.ne', hℓ, one_div, Real.log_inv]; push_cast; ring
    have hlogL : 0 ≤ Real.log L' := Real.log_nonneg hL'1
    have hpow : (Real.pi * (L' * ρ) ^ 2) ^ d = A * ρ ^ (2 * d) := by
      rw [hA, mul_pow, ← mul_pow, pow_mul]; ring
    rw [hpow, hlog]
    have hJ0 : 0 ≤ J⁻¹ := by positivity
    have : 1 - 2 * (2 * Real.log L' - 2 * ℓ) ≤ 4 * (1 + ℓ) := by linarith
    calc J⁻¹ * (A * ρ ^ (2 * d) * (1 - 2 * (2 * Real.log L' - 2 * ℓ)))
        ≤ J⁻¹ * (A * ρ ^ (2 * d) * (4 * (1 + ℓ))) := by gcongr
      _ = _ := by ring

  have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball v ρ)),
      f x = H x - ∑ i ∈ I, Real.log (‖Ψ x i‖ ^ 2) ∧ x ∈ Metric.ball v ρ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hbS hnz, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxb
    refine ⟨?_, hxb⟩
    rw [hf x (hrU (hbS hxb)) (fun i _ => hx i)]
    simp only [hΨi]
  have hHm : AEMeasurable H (volume.restrict (Metric.ball v ρ)) :=
    (hH.mono (hbS.trans hrU)).aemeasurable Metric.isOpen_ball.measurableSet
  have hΨm' : AEMeasurable Ψ (volume.restrict (Metric.ball v ρ)) :=
    (hcS.mono hbS).aemeasurable Metric.isOpen_ball.measurableSet
  have hFm : AEMeasurable (fun x => H x - ∑ i ∈ I, Real.log (‖Ψ x i‖ ^ 2)) (volume.restrict (Metric.ball v ρ)) := by
    refine hHm.sub (Finset.aemeasurable_fun_sum _ fun i _ => ?_)
    have : Measurable fun w : ReciprocityTheory.L2DbarEstimates.V d => Real.log (‖w i‖ ^ 2) := by
      have := (coord_cont i).measurable
      fun_prop
    exact this.comp_aemeasurable hΨm'
  have hfm : AEStronglyMeasurable f (volume.restrict (Metric.ball v ρ)) :=
    hFm.aestronglyMeasurable.congr (hae.mono fun x hx => hx.1.symm)
  have hbint : IntegrableOn (fun x => M + ∑ i ∈ I, max 0 (-Real.log (‖Ψ x i‖ ^ 2))) (Metric.ball v ρ) :=
    (integrableOn_const measure_ball_lt_top.ne).add (integrable_finset_sum I fun i _ => (hcoord i).1)
  have hle : ∀ᵐ x ∂(volume.restrict (Metric.ball v ρ)),
      ‖f x‖ ≤ M + ∑ i ∈ I, max 0 (-Real.log (‖Ψ x i‖ ^ 2)) := by
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x), hx.1, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    have hHx : H x ≤ M := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x (hball hx.2))
    gcongr with i
    exact le_max_right _ _
  have hint : IntegrableOn f (Metric.ball v ρ) := hbint.mono' hfm hle
  have hci : Integrable (fun _ => M) (volume.restrict (Metric.ball v ρ)) := integrableOn_const measure_ball_lt_top.ne
  refine ⟨hint, ?_⟩
  have hvol : volume.real (Metric.ball v ρ) = ρ ^ (2 * d) * c := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume v hρ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      hc, measureReal_def, finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  calc ∫ y in Metric.ball v ρ, f y
      ≤ ∫ y in Metric.ball v ρ, (M + ∑ i ∈ I, max 0 (-Real.log (‖Ψ y i‖ ^ 2))) :=
        integral_mono_ae hint hbint (hle.mono fun x hx => (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hx))
    _ = volume.real (Metric.ball v ρ) * M + ∑ i ∈ I, ∫ y in Metric.ball v ρ, max 0 (-Real.log (‖Ψ y i‖ ^ 2)) := by
        rw [integral_add hci (integrable_finset_sum I fun i _ => (hcoord i).1),
          integral_finset_sum I fun i _ => (hcoord i).1, setIntegral_const, smul_eq_mul]
    _ ≤ ρ ^ (2 * d) * c * max M 0 + ∑ i ∈ I, J⁻¹ * A * 4 * (ρ ^ (2 * d) * (1 + ℓ)) := by
        rw [hvol]
        gcongr with i
        · exact le_max_left _ _
        · exact (hcoord i).2
    _ ≤ (max M 0 * c + I.card * (J⁻¹ * A * 4)) * ρ ^ (2 * d) * (1 + ℓ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have h1 : ρ ^ (2 * d) * c * max M 0 ≤ ρ ^ (2 * d) * c * max M 0 * (1 + ℓ) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        nlinarith [h1]

end GlobalTheory.LogModel
