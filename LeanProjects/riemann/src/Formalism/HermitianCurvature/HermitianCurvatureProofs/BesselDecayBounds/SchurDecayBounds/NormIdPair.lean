import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdCore

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem hs_one {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    {u v : H} (ξ : Wp) {x : Mx k r} (hx : x ∈ UH (Hpk k r))
    (hint : Integrable (beF z c π σ (σ x u) v) (μW.prod μN)) :
    Integrable (fun p => Fx z c π μW μN σ u v ξ (sM p * x)) (μW.prod μN) ∧
      ((‖Aop z c π μW μN σ u v x ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p, Fx z c π μW μN σ u v ξ (sM p * x) ∂(μW.prod μN) := by
  set A : Wp →L[ℂ] Wp := Aop z c π μW μN σ u v x with hA
  have hiso : ∀ b ∈ UWset k r z, ∀ y y' : Wp, ⟪π b y, π b y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro b hb y y'
    let T : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π b : Wp →ₗ[ℂ] Wp), norm_map' := hPi.2.2 b hb }
    exact T.inner_map_map y y'
  have hadj : ∀ b ∈ UWset k r z, ∀ y y' : Wp, ⟪π b y, y'⟫_ℂ = ⟪y, π b⁻¹ y'⟫_ℂ := by
    intro b hb y y'
    have hbinv : b⁻¹ ∈ UWset k r z := hGr.2.2.1 b hb
    have h1 : b * b⁻¹ = 1 := (hGr.2.1 b hb.1).1
    have h2 : π b (π b⁻¹ y') = y' := by
      have h3 := hPi.2.1 b hb b⁻¹ hbinv
      rw [h1, hPi.1] at h3
      have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T y') h3
      simpa using h4.symm
    calc ⟪π b y, y'⟫_ℂ = ⟪π b y, π b (π b⁻¹ y')⟫_ℂ := by rw [h2]
      _ = ⟪y, π b⁻¹ y'⟫_ℂ := hiso b hb y _
  have hc : ∀ y y' : Wp, star ⟪y, y'⟫_ℂ = ⟪y', y⟫_ℂ := fun y y' => inner_conj_symm y' y
  have key : ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ UWset k r z → Matrix.of p.2 ∈ Nset k r →
      Fx z c π μW μN σ u v ξ (sM p * x) = ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ := by
    intro p h1 h2
    have hmul : sM p ∈ UH (Hpk k r) := hGr.1 _ h1.1 _ h2.1
    have hσ' : σ (sM p * x) u = σ (Matrix.of p.1 * Matrix.of p.2) (σ x u) := by
      rw [hSg.2.1 _ hmul _ hx]; rfl
    have heq : Aop z c π μW μN σ u v (sM p * x) =
        (psi k r z c (Matrix.of p.2) • π (Matrix.of p.1)).comp A := by
      show be z c π μW μN σ (σ (sM p * x) u) v = _
      rw [hσ']
      exact be_equiv_of_int hGr hSg hPi hPs hM hint h1 h2
    rw [show Fx z c π μW μN σ u v ξ (sM p * x) =
        ⟪v, σ (sM p * x) u⟫_ℂ * star ⟪ξ, Aop z c π μW μN σ u v (sM p * x) ξ⟫_ℂ from rfl]
    rw [show beF z c π σ (σ x u) v p = (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ x u)⟫_ℂ *
        star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ from rfl]
    rw [heq, hσ', ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, inner_smul_right, star_mul', hc,
      ← hadj _ h1]
    ring
  have hae : (fun p => Fx z c π μW μN σ u v ξ (sM p * x)) =ᵐ[μW.prod μN]
      fun p => ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ := by
    filter_upwards [hM.1] with p hp
    exact key p hp.1 hp.2
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ (A ξ)).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪A ξ, T ξ⟫_ℂ := fun T => by simp [L]
  have hLint : Integrable (fun p => L (beF z c π σ (σ x u) v p)) (μW.prod μN) := L.integrable_comp hint
  have hint2 : Integrable (fun p => ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ) (μW.prod μN) := by
    simpa only [hL] using hLint
  refine ⟨hint2.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  have hI : ∫ p, ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ ∂(μW.prod μN) = ⟪A ξ, A ξ⟫_ℂ := by
    simp_rw [← hL]
    rw [L.integral_comp_comm hint, hL]
    rfl
  rw [hI, inner_self_eq_norm_sq_to_K]
  norm_num

theorem normId_pair {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : GHyp z π μW μN μG ν σ)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {u v : H} (hu : u ≠ 0)
    (hI : ∀ x ∈ UH (Hpk k r), Integrable (beF z c π σ (σ x u) v) (μW.prod μN))
    (hIv : Integrable (beF z c π σ v v) (μW.prod μN))
    (hD : Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖) (μG.prod (μW.prod μN)))
    (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u := by
  have hnu := nuStep k r H Wp z π μW μN μG ν σ hG
  obtain ⟨⟨ε, lam, -, hds⟩, hHaar, -, -, ⟨-, hW1⟩, ⟨κ0, -, -, rfl⟩, -⟩ := id hG
  have : IsFiniteMeasure μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have : SFinite μG := sfinite_haar hHaar
  obtain ⟨d, hd, hSch⟩ := id hS
  rw [fdegH_eq ⟨hd, hSch⟩ hu]
  set μS := μW.prod (haarLie (Nset k r) κ0) with hμS
  set Φ : Mt k r × (Mt k r × Mt k r) → ℂ := fun q =>
    ⟪v, σ (Matrix.of q.1) u⟫_ℂ * star ⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ * kx z c π ξ q.2 with hΦdef
  have h1 : ∀ᵐ y ∂μG, Fx z c π μW (haarLie (Nset k r) κ0) σ u v ξ (Matrix.of y) = ∫ p, Φ (y, p) ∂μS := by
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
  have hF : Integrable (fun y : Mt k r => Fx z c π μW (haarLie (Nset k r) κ0) σ u v ξ (Matrix.of y)) μG :=
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
  have hFG : ∫ y, Fx z c π μW (haarLie (Nset k r) κ0) σ u v ξ (Matrix.of y) ∂μG =
      ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW (haarLie (Nset k r) κ0) σ v v ξ⟫_ℂ := by
    rw [integral_congr_ae h1, integral_integral_swap (f := fun y p => Φ (y, p)) hΦ,
      integral_congr_ae h4, integral_const_mul, ← star_ev_be hIv ξ]
  obtain ⟨-, hint, heq⟩ := weilStep k r H Wp z π μW (haarLie (Nset k r) κ0) μG ν σ hG
    (Fx z c π μW (haarLie (Nset k r) κ0) σ u v ξ) hF
  have hpt : ∀ᵐ x ∂ν, ‖be z c π μW (haarLie (Nset k r) κ0) σ (σ (Matrix.of x) u) v ξ‖ ^ 2 =
      (∫ p, Fx z c π μW (haarLie (Nset k r) κ0) σ u v ξ (sM p * Matrix.of x) ∂μS).re := by
    filter_upwards [hnu] with x hx
    rw [← (hs_one hGr hSg hPi hPs hM ξ hx (hI _ hx)).2, Complex.ofReal_re]
    rfl
  refine ⟨hint.re.congr (hpt.mono fun x hx => hx.symm), ?_⟩
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [integral_congr_ae hpt, hre, ← heq, hFG]
  have e3 : ((‖u‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) * star ⟪ξ, be z c π μW (haarLie (Nset k r) κ0) σ v v ξ⟫_ℂ =
      (((‖u‖ ^ 2 / d : ℝ)) : ℂ) * ⟪be z c π μW (haarLie (Nset k r) κ0) σ v v ξ, ξ⟫_ℂ := by
    rw [star_inner]
    push_cast
    ring
  rw [e3, Complex.re_ofReal_mul]
  ring

end PI.WBL.NIS
