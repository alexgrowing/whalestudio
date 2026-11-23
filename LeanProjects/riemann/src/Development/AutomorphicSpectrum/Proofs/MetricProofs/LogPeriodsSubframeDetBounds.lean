import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SubframeDetLogGrowth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivializationStatement
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent

open Matrix Metric GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open scoped ComplexOrder

theorem frame_rank_of_gram_det_ne_zero {g k : ℕ} (M : Matrix (Fin g) (Fin k) ℂ)
    (h : (Mᵀ * M.map star).det ≠ 0) : M.rank = k := by
  have hu : IsUnit (Mᵀ * M.map star) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left Mᵀ (M.map star)
  rw [Matrix.rank_transpose] at h2
  have h3 := M.rank_le_width
  omega

theorem frame_compact_nhd {g k : ℕ} (M₀ : Matrix (Fin g) (Fin k) ℂ) (h : M₀.rank = k) :
    ∃ S : Set (Matrix (Fin g) (Fin k) ℂ), IsCompact S ∧ S ∈ nhds M₀ ∧ ∀ M ∈ S, M.rank = k := by
  have hP : (M₀.map star)ᴴ = M₀ᵀ := by
    ext i j
    simp
  have hpos : 0 < ((M₀ᵀ * M₀.map star).det).re := by
    have := GlobalTheory.re_det_pos_of_posDef (subframe_gram_posDef M₀ h)
    rw [hP] at this
    exact this
  have hU : IsOpen {M : Matrix (Fin g) (Fin k) ℂ | 0 < ((Mᵀ * M.map star).det).re} :=
    isOpen_lt continuous_const subframe_continuous_det
  haveI : LocallyCompactSpace (Matrix (Fin g) (Fin k) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin g → Fin k → ℂ))
  obtain ⟨S, hS, hSU, hSc⟩ := local_compact_nhds (hU.mem_nhds hpos)
  refine ⟨S, hSc, hS, fun M hM => frame_rank_of_gram_det_ne_zero M ?_⟩
  intro h0
  have := hSU hM
  rw [Set.mem_setOf_eq, h0] at this
  simp at this

theorem continuousAt_matrix_inv {X : Type*} [TopologicalSpace X] {g : ℕ}
    (A : X → Matrix (Fin g) (Fin g) ℂ) (x : X) (hA : ContinuousAt A x) (h : (A x).det ≠ 0) :
    ContinuousAt (fun y => (A y)⁻¹) x := by
  have hd : ContinuousAt (fun y => (A y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hA
  have ha : ContinuousAt (fun y => (A y).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hd.inv₀ h).smul ha

theorem chartRadius_le_log_sum {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (h1 : ∀ k, ‖z k‖ < 1)
    (h0 : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    1 ≤ chartRadius h z ∧ chartRadius h z ≤ (Real.exp 1 + 2) *
      (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) := by
  have hsum : ∑ j : Fin a, |Real.log ‖z (Fin.castLE h j)‖| =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro j _ j' _ e
      exact Fin.castLE_injective h e
    · intro i hi
      have hi' : i.val < a := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
    · intro j _
      rfl
  have hterm : ∀ j : Fin a, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ =
      2 * |Real.log ‖z (Fin.castLE h j)‖| := by
    intro j
    have hc : cuspCoord h z j = z (Fin.castLE h j) := rfl
    have hn : 0 ≤ ‖z (Fin.castLE h j)‖ := norm_nonneg _
    rw [hc, Real.log_inv, Real.log_pow, abs_of_nonpos (Real.log_nonpos hn (h1 _).le)]
    push_cast
    ring
  have hr : chartRadius h z = Real.exp 1 + 2 *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    rw [chartRadius, ← hsum, Finset.mul_sum]
    simp only [hterm]
  have hS : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [hr]
  constructor
  · linarith
  · nlinarith

theorem logPeriods_subframe_det_bounds : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ) (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ), ContinuousAt F 0 → (F 0).rank = k → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i : Fin n, i.val < a → z i ≠ 0) → ‖(F z * L.H z * (F z)ᴴ).det‖ ≤ K ∧ 1 ≤ K * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) ^ N * ‖(F z * L.H z * (F z)ᴴ).det‖ := by
  intro n a g Λ _ L k F hF hrk
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := GlobalTheory.T.period_matrix_local_trivialization n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hAi := continuousAt_matrix_inv A 0 hAc hA0
  have hc2 : Continuous (fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hmul : ContinuousAt (fun z => F z * (A z)⁻¹) 0 :=
    ContinuousAt.comp (g := fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2)
      (f := fun z => (F z, (A z)⁻¹)) hc2.continuousAt (hF.prodMk hAi)
  have hG : ContinuousAt (fun z => (F z * (A z)⁻¹)ᵀ) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hmul
  have hM0 : ((F 0 * (A 0)⁻¹)ᵀ).rank = k := by
    have hu : IsUnit ((A 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hA0)
    rw [Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, hrk]
  obtain ⟨S, hS, hSn, hSr⟩ := frame_compact_nhd _ hM0
  obtain ⟨C', hC', hd⟩ := subframe_det_log_growth g k (Matrix (Fin g) (Fin k) ℂ) S hS id
    continuousOn_id hSr c C hc
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  have hev : ∀ᶠ z in nhds (0 : Fin n → ℂ), (F z * (A z)⁻¹)ᵀ ∈ S ∧ (A z).det ≠ 0 :=
    (hG.eventually_mem hSn).and (hdet.eventually_ne hA0)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨min (min ρ₁ ρ₂) 1, C' * (Real.exp 1 + 2) ^ k, k, lt_min (lt_min hρ₁ hρ₂) one_pos,
    min_le_right _ _, fun z hz hz0 => ?_⟩
  have hzρ : ‖z‖ < min (min ρ₁ ρ₂) 1 := by simpa [dist_zero_right] using hz
  have hz1n : ‖z‖ < 1 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz1n
  have hzρ₁ : z ∈ closedBall (0 : Fin n → ℂ) ρ₁ := by
    have : ‖z‖ ≤ ρ₁ := hzρ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    simpa [dist_zero_right] using this
  have hzρ₂ : z ∈ ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hzρ ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  obtain ⟨hGS, hAz⟩ := hball z hzρ₂
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (ball (0 : Fin n → ℂ) 1) :=
    ⟨by simpa [dist_zero_right] using hz1n, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hAHz := hAH _ hw
  rw [hexp] at hAHz
  obtain ⟨hb1, hb2⟩ := hb _ hw (by rw [hexp]; exact hzρ₁)
  rw [hexp] at hb2
  obtain ⟨hr1, hr2⟩ := chartRadius_le_log_sum L.a_le z hz1 hz0
  have hx := hd _ hGS ((Q.τ (logLift a z)).map Complex.im) (chartRadius L.a_le z) hr1 hb1 hb2
  set Y := (Q.τ (logLift a z)).map Complex.im with hY
  set S' := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| with hS'
  have hAu : IsUnit (A z).det := isUnit_iff_ne_zero.2 hAz
  have hinv1 : (A z)⁻¹ * A z = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : (A z)ᴴ * ((A z)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hkey : F z * L.H z * (F z)ᴴ = (F z * (A z)⁻¹) * (Y⁻¹).map Complex.ofReal * (F z * (A z)⁻¹)ᴴ := by
    rw [← hAHz, Matrix.conjTranspose_mul]
    have e : F z * (A z)⁻¹ * (A z * L.H z * (A z)ᴴ) * (((A z)⁻¹)ᴴ * (F z)ᴴ) =
        F z * ((A z)⁻¹ * A z) * L.H z * ((A z)ᴴ * ((A z)⁻¹)ᴴ) * (F z)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have hd1 : ((F z * L.H z * (F z)ᴴ).det).re ≤ C' := by
    rw [hkey]
    exact hx.1
  have hd2 : 1 ≤ C' * chartRadius L.a_le z ^ k * ((F z * L.H z * (F z)ᴴ).det).re := by
    rw [hkey]
    exact hx.2
  have hpsd : (F z * L.H z * (F z)ᴴ).PosSemidef := by
    rw [hkey]
    have hYp : Y.PosDef := Q.im_posDef _ hw
    exact (subframe_map_posSemidef hYp.inv.posSemidef).mul_mul_conjTranspose_same _
  have hD := hpsd.det_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hDdef] at hd1 hd2 hD ⊢
  have hnorm : ‖D‖ = D.re := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hD
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [h2.symm]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg h1]
  rw [hnorm]
  have hre : 0 ≤ D.re := (Complex.nonneg_iff.1 hD).1
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE1 : 1 ≤ (Real.exp 1 + 2) ^ k := one_le_pow₀ (by linarith [Real.exp_pos 1])
  constructor
  · calc D.re ≤ C' := hd1
      _ ≤ C' * (Real.exp 1 + 2) ^ k := le_mul_of_one_le_right hC'.le hE1
  · have hpow : chartRadius L.a_le z ^ k ≤ ((Real.exp 1 + 2) * (1 + S')) ^ k :=
      pow_le_pow_left₀ (by linarith) hr2 k
    calc (1 : ℝ) ≤ C' * chartRadius L.a_le z ^ k * D.re := hd2
      _ ≤ C' * ((Real.exp 1 + 2) * (1 + S')) ^ k * D.re := by gcongr
      _ = C' * (Real.exp 1 + 2) ^ k * (1 + S') ^ k * D.re := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Flat
