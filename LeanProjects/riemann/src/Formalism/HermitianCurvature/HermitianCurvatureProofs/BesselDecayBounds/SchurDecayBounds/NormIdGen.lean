import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdPair

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

variable {k r : ℕ}

theorem weilGen {μG μW μN ν : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hHaar : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muSof μW μN) ν)
    (F : Mx k r → ℂ) (hF : Integrable (fun x : Mt k r => F (Matrix.of x)) μG) :
    (∀ᵐ x ∂ν, Integrable (fun p => F (sM p * Matrix.of x)) (μW.prod μN)) ∧
    Integrable (fun x : Mt k r => ∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ν ∧
    ∫ x, F (Matrix.of x) ∂μG = ∫ x, (∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ∂ν := by
  haveI : SigmaFinite μG := hHaar.1
  haveI : SFinite (muSof μW μN) := by unfold muSof; infer_instance
  haveI : SFinite ν := sfinite_quot hHaar.2.1 hq
  have hmap := quot_map hq
  rw [hmap] at hF
  have hF' : Integrable ((fun x : Mt k r => F (Matrix.of x)) ∘ psiMap) (ν.prod (μW.prod μN)) :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_psiMap.aemeasurable).1 hF
  refine ⟨hF'.prod_right_ae, hF'.integral_prod_left, ?_⟩
  rw [hmap, integral_map measurable_psiMap.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ hF'

theorem nuGen {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hHaar : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muSof μW μN) ν)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk k r) := by
  have : SigmaFinite μG := hHaar.1
  have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
  have : SFinite ν := sfinite_quot hHaar.2.1 hq
  have hmap := quot_map hq
  have hGm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} :=
    ((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet
  have hGc : μG {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = 0 := hHaar.2.2.1
  have hGm' : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} := hGm.compl
  rw [hmap, Measure.map_apply measurable_psiMap hGm'] at hGc
  have hae : ∀ᵐ q ∂(ν.prod (μW.prod μN)), Matrix.of (psiMap q) ∈ UH (Hpk k r) := ae_iff.mpr hGc
  have hae2 := Measure.ae_ae_of_ae_prod hae
  have hS : ∀ᵐ p ∂(μW.prod μN), sM p ∈ UH (Hpk k r) := by
    filter_upwards [hM1] with p hp
    exact PI.WUN.UH_mul hp.1.1 hp.2.1
  have hμ0 : μW.prod μN ≠ 0 := by
    intro h0
    apply muS_ne_zero hHaar.2.1 hq
    unfold muSof
    rw [h0, Measure.map_zero]
  filter_upwards [hae2] with x hx
  by_contra hxG
  have hfalse : ∀ᵐ p ∂(μW.prod μN), False := by
    filter_upwards [hx, hS] with p hp hsp
    apply hxG
    have hp' : sM p * Matrix.of x ∈ UH (Hpk k r) := hp
    have : Matrix.of x = (sM p)⁻¹ * (sM p * Matrix.of x) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (PI.WUN.UH_det hsp), Matrix.one_mul]
    rw [this]
    exact PI.WUN.UH_mul (PI.WUN.UH_inv hsp) hp'
  apply hμ0
  rw [ae_iff] at hfalse
  simpa using hfalse

theorem normId_gen {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] {σ : Mx k r → (H →L[ℂ] H)}
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} (hds : IsDSHpk k r ε lam σ)
    (hHaar : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muSof μW μN) ν)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {u v : H} (hu : u ≠ 0)
    (hI : ∀ x ∈ UH (Hpk k r), Integrable (beF z c π σ (σ x u) v) (μW.prod μN))
    (hIv : Integrable (beF z c π σ v v) (μW.prod μN))
    (hD : Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖) (μG.prod (μW.prod μN)))
    (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    (⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ).im = 0 := by
  have hnu := nuGen hHaar hq hM.1
  have : SFinite μG := sfinite_haar hHaar
  obtain ⟨d, hd, hSch⟩ := id hS
  rw [fdegH_eq ⟨hd, hSch⟩ hu]
  set μS := μW.prod (μN) with hμS
  set Φ : Mt k r × (Mt k r × Mt k r) → ℂ := fun q =>
    ⟪v, σ (Matrix.of q.1) u⟫_ℂ * star ⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ * kx z c π ξ q.2 with hΦdef
  have h1 : ∀ᵐ y ∂μG, Fx z c π μW (μN) σ u v ξ (Matrix.of y) = ∫ p, Φ (y, p) ∂μS := by
    filter_upwards [ae_UH_of_haar hHaar] with y hy
    unfold Fx Aop
    rw [star_ev_be (hI _ hy) ξ, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hM.1] with p hp
    have hs : sM p ∈ UH (Hpk k r) := hGr.1 _ hp.1.1 _ hp.2.1
    show _ = ⟪v, σ (Matrix.of y) u⟫_ℂ * star ⟪v, σ (sM p * Matrix.of y) u⟫_ℂ * kx z c π ξ p
    rw [hSg.2.1 _ hs _ hy, ContinuousLinearMap.comp_apply]
    ring
  have hΦ : Integrable Φ (μG.prod μS) := by
    refine Integrable.mono' (hD.const_mul (‖ξ‖ ^ 2)) ?_ ?_
    · have m1 : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (Matrix.of q.1) u⟫_ℂ)
          (μG.prod μS) := (coef_aesm hds hHaar u v).comp_fst
      have m2 := matrix_coefficient_ae_strongly_measurable hds hGr hHaar hM.1 u v
      have m3 : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) => kx z c π ξ q.2) (μG.prod μS) :=
        (kx_aesm hM ξ).comp_snd
      exact (m1.mul (continuous_star.comp_aestronglyMeasurable m2)).mul m3
    · filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μG) (ν := μS)).ae hM.1] with q hq
      have hk := norm_kx_le (c := c) hGr hPi ξ hq.1
      simp only [Φ, norm_mul, norm_star]
      calc ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ * ‖kx z c π ξ q.2‖
          ≤ ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ * ‖ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = ‖ξ‖ ^ 2 * (‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖) := by ring
  have hF : Integrable (fun y : Mt k r => Fx z c π μW (μN) σ u v ξ (Matrix.of y)) μG :=
    hΦ.integral_prod_left.congr (h1.mono fun y hy => hy.symm)
  have hu2 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have h4 : ∀ᵐ p ∂μS, ∫ y, Φ (y, p) ∂μG =
      ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * (star ⟪v, σ (sM p) v⟫_ℂ * kx z c π ξ p) := by
    filter_upwards [hM.1] with p hp
    have hs : sM p ∈ UH (Hpk k r) := hGr.1 _ hp.1.1 _ hp.2.1
    have hsi : (sM p)⁻¹ ∈ UH (Hpk k r) := (hGr.2.1 _ hs).2.2
    have hss : sM p * (sM p)⁻¹ = 1 := (hGr.2.1 _ hs).1
    have hadj : ContinuousLinearMap.adjoint (σ (sM p)) = σ (sM p)⁻¹ :=
      Cv.adjoint_eq_of_iso _ _ (hSg.2.2 _ hs) (by rw [← hSg.2.1 _ hs _ hsi, hss, hSg.1])
    have e0 : ∀ w : H, ⟪v, σ (sM p) w⟫_ℂ = ⟪σ (sM p)⁻¹ v, w⟫_ℂ := fun w => by
      rw [← hadj, ContinuousLinearMap.adjoint_inner_left]
    have hcongr : ∀ᵐ y ∂μG, Φ (y, p) =
        kx z c π ξ p * (⟪v, σ (Matrix.of y) u⟫_ℂ * star ⟪σ (sM p)⁻¹ v, σ (Matrix.of y) u⟫_ℂ) := by
      filter_upwards [ae_UH_of_haar hHaar] with y hy
      show ⟪v, σ (Matrix.of y) u⟫_ℂ * star ⟪v, σ (sM p * Matrix.of y) u⟫_ℂ * kx z c π ξ p = _
      rw [hSg.2.1 _ hs _ hy, ContinuousLinearMap.comp_apply, e0]
      ring
    rw [integral_congr_ae hcongr, integral_const_mul, (hSch u v u (σ (sM p)⁻¹ v)).2]
    have e1 : ⟪v, σ (sM p)⁻¹ v⟫_ℂ = star ⟪v, σ (sM p) v⟫_ℂ := by
      rw [← hadj, ContinuousLinearMap.adjoint_inner_right, star_inner]
    rw [e1, hu2]
    ring
  have hFG : ∫ y, Fx z c π μW (μN) σ u v ξ (Matrix.of y) ∂μG =
      ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW (μN) σ v v ξ⟫_ℂ := by
    rw [integral_congr_ae h1, integral_integral_swap (f := fun y p => Φ (y, p)) hΦ,
      integral_congr_ae h4, integral_const_mul, ← star_ev_be hIv ξ]
  obtain ⟨-, hint, heq⟩ := weilGen hHaar hq (Fx z c π μW μN σ u v ξ) hF
  have hpt : ∀ᵐ x ∂ν, ‖be z c π μW (μN) σ (σ (Matrix.of x) u) v ξ‖ ^ 2 =
      (∫ p, Fx z c π μW (μN) σ u v ξ (sM p * Matrix.of x) ∂μS).re := by
    filter_upwards [hnu] with x hx
    rw [← (hs_one hGr hSg hPi hPs hM ξ hx (hI _ hx)).2, Complex.ofReal_re]
    rfl
  have hC : ((∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν : ℝ) : ℂ) =
      ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ := by
    rw [← integral_complex_ofReal, ← hFG, heq]
    refine integral_congr_ae ?_
    filter_upwards [hnu] with x hx
    exact (hs_one hGr hSg hPi hPs hM ξ hx (hI _ hx)).2
  have him : (⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ).im = 0 := by
    have h1 := congrArg Complex.im hC
    have e3 : ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ =
        (((‖u‖ ^ 2 / d : ℝ)) : ℂ) * star ⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ := by
      push_cast
      ring
    rw [e3, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.star_def, Complex.conj_im] at h1
    have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hne : ‖u‖ ^ 2 / d ≠ 0 := by positivity
    have h2 : ‖u‖ ^ 2 / d * (⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ).im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hne
    · exact h
  refine ⟨hint.re.congr (hpt.mono fun x hx => hx.symm), ?_, him⟩
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [integral_congr_ae hpt, hre, ← heq, hFG]
  have e3 : ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW (μN) σ v v ξ⟫_ℂ =
      (((‖u‖ ^ 2 / d : ℝ)) : ℂ) * ⟪be z c π μW (μN) σ v v ξ, ξ⟫_ℂ := by
    rw [star_inner]
    push_cast
    ring
  rw [e3, Complex.re_ofReal_mul]
  ring

end PI.WBL.NIS
