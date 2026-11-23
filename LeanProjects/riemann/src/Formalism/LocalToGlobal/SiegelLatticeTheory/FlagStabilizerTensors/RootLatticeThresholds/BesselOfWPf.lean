import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNonvanishingFromL2

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.MainNotions.BridgeCS3dBOW

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem orbit_data {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (hWh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hNh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    {W : Mx k r → Wp} (hWc : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hWeq : PI.BesselPeriodGGP.IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    {x0 : Mx k r} (hx0 : x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r =>
      PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of y) • W (x0 * Matrix.of y)) μG)
    (hR : PI.BesselPeriodGGP.rconv μG (PI.BesselPeriodGGP.eFun μG σ w0) W x0 = W x0) (η : Wp) :
    ∃ Φ : Formalism.QuantumDeterminants.Mt k r → ℂ, Measurable Φ ∧ Integrable Φ μG ∧ ∫ g, Φ g ∂μG = ⟪η, W x0⟫_ℂ ∧
      ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
        ∀ᵐ p ∂(μW.prod μN), Φ (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
          ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) *
            ⟪beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η, W (Matrix.of x)⟫_ℂ := by
  classical
  have := hWh.1; have := hNh.1; have := hGh.1
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0
  obtain ⟨hxi, hxx, hxx'⟩ := uh_inv hx0
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  have hUm : MeasurableSet U := (isClosed_UH.preimage hof).measurableSet
  let Φ : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g =>
    ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ
  let Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ := U.piecewise Φ (fun _ => 0)
  have hΦc : ContinuousOn Φ U := by
    have hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U :=
      (continuous_const.matrix_mul hof).continuousOn
    have hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := fun g hg => DDSmoothness.uh_mul hxi hg
    have he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
        PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U := by
      unfold PI.BesselPeriodGGP.eFun
      exact continuousOn_const.mul (continuous_star.comp_continuousOn
        (continuousOn_const.inner (hcs.comp hm hmaps)))
    have hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U :=
      hWc.comp hof.continuousOn (fun g hg => hg)
    exact continuousOn_const.inner (he.smul hWc')
  have hΦm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hUm
  have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := continuous_const.matrix_mul hof
    exact this.measurable
  have htrans : (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG]
      Φ' ∘ Formalism.QuantumDeterminants.lmulM x0 := by
    filter_upwards [hGae] with g hg
    have hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hx0 hg
    have hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U := hxg
    simp only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]
    show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
    rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
  have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
  have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
    (innerSL ℂ η).integrable_comp hI
  have hΦint : Integrable Φ' μG := by
    have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
    rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
    exact h2
  refine ⟨Φ', hΦm, hΦint, ?_, ?_⟩
  · have e1 : ⟪η, W x0⟫_ℂ = ∫ g, ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ ∂μG := by
      conv_lhs => rw [← hR]
      unfold PI.BesselPeriodGGP.rconv
      rw [integral_inner hI η]
    rw [e1, integral_congr_ae htrans]
    show ∫ g, Φ' g ∂μG = ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
  · intro x hx
    filter_upwards [hPae] with p hp
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hs hx
    have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
    simp only [Φ', Set.piecewise, hmem, if_true, Φ]
    show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) •
        W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _
    rw [hWeq _ hp.1 _ hp.2 _ hx]
    have hdet : IsUnit x0.det := Matrix.isUnit_det_of_right_inverse hxx
    have eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 =
        σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u') := by
      rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]; rfl
    have eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ =
        ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ := by
      rw [eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]
    unfold PI.BesselPeriodGGP.eFun beInt
    rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply,
      inner_smul_left]
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    ring

theorem g_int {σ : Mx k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {l : H → Wp} {u' v' : H}
    (hI : Integrable (beInt z c π σ u' v') (μW.prod μN))
    (hE : ∫ p, beInt z c π σ u' v' p ∂(μW.prod μN) = (innerSL ℂ (l v')).smulRight (l u')) (η w : Wp) :
    Integrable (fun p => ⟪w, beInt z c π σ u' v' p η⟫_ℂ) (μW.prod μN) ∧
      ∫ p, ⟪w, beInt z c π σ u' v' p η⟫_ℂ ∂(μW.prod μN) = ⟪l v', η⟫_ℂ * ⟪w, l u'⟫_ℂ := by
  have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
    (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI
  refine ⟨(innerSL ℂ w).integrable_comp hf, ?_⟩
  rw [integral_inner hf w, ← ContinuousLinearMap.integral_apply hI η, hE, ContinuousLinearMap.smulRight_apply,
    inner_smul_right]
  rfl

theorem bow_core [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) (l : H → Wp)
    (hl : ∀ u' ∈ DDsp σ w0, ∀ v' ∈ DDsp σ w0, Integrable (beInt z c π σ u' v') (μW.prod μN) ∧
      ∫ p, beInt z c π σ u' v' p ∂(μW.prod μN) = (innerSL ℂ (l v')).smulRight (l u'))
    {W : Mx k r → Wp} (hWc : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hWeq : PI.BesselPeriodGGP.IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hRe : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun y : Formalism.QuantumDeterminants.Mt k r =>
        PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of y) • W (x * Matrix.of y)) μG ∧
      PI.BesselPeriodGGP.rconv μG (PI.BesselPeriodGGP.eFun μG σ w0) W x = W x) :
    ∃ κ : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = κ • l (σ x w0) := by
  classical
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hsf : SFinite (muSof μW μN) := by unfold muSof; infer_instance
  have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
    exact h3.measurable
  have comb : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ η0 η1 : Wp,
      ∀ b0 b1 : ℂ, (starRingEnd ℂ) b0 * ⟪l (σ x0 w0), η0⟫_ℂ = (starRingEnd ℂ) b1 * ⟪l (σ x1 w0), η1⟫_ℂ →
      b0 * ⟪η0, W x0⟫_ℂ = b1 * ⟪η1, W x1⟫_ℂ := by
    intro x0 hx0 x1 hx1 η0 η1 b0 b1 hb
    obtain ⟨Φ0, hm0, hi0, he0, ho0⟩ :=
      orbit_data hσ hT hπ hWh hNh hGh hWc hWeq hx0 (hRe x0 hx0).1 (hRe x0 hx0).2 η0
    obtain ⟨Φ1, hm1, hi1, he1, ho1⟩ :=
      orbit_data hσ hT hπ hWh hNh hGh hWc hWeq hx1 (hRe x1 hx1).1 (hRe x1 hx1).2 η1
    let F : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g => b0 * Φ0 g - b1 * Φ1 g
    have hFm : Measurable F := (measurable_const.mul hm0).sub (measurable_const.mul hm1)
    have hFi : Integrable F μG := (hi0.const_mul b0).sub (hi1.const_mul b1)
    have hF0 : ∫ g, F g ∂μG = 0 := by
      refine quot_zero hq F hFm hFi ?_
      filter_upwards [hνae] with x hx
      have hFm' : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => F (mulMt s x)) :=
        hFm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
      unfold muSof
      rw [integral_map hpm.aemeasurable hFm'.aestronglyMeasurable]
      obtain ⟨hI0, hE0⟩ := hl (σ (Matrix.of x) w0) (memDD _ hx) (σ x0 w0) (memDD _ hx0)
      obtain ⟨hI1, hE1⟩ := hl (σ (Matrix.of x) w0) (memDD _ hx) (σ x1 w0) (memDD _ hx1)
      obtain ⟨hg0, e0⟩ := g_int hI0 hE0 η0 (W (Matrix.of x))
      obtain ⟨hg1, e1⟩ := g_int hI1 hE1 η1 (W (Matrix.of x))
      have hval : ∀ᵐ p ∂(μW.prod μN), F (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
          ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * (starRingEnd ℂ)
            ((starRingEnd ℂ) b0 * ⟪W (Matrix.of x), beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η0⟫_ℂ -
            (starRingEnd ℂ) b1 * ⟪W (Matrix.of x), beInt z c π σ (σ (Matrix.of x) w0) (σ x1 w0) p η1⟫_ℂ) := by
        filter_upwards [ho0 x hx, ho1 x hx] with p h0p h1p
        show b0 * Φ0 _ - b1 * Φ1 _ = _
        rw [h0p, h1p, ← inner_conj_symm (beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η0) (W (Matrix.of x)),
          ← inner_conj_symm (beInt z c π σ (σ (Matrix.of x) w0) (σ x1 w0) p η1) (W (Matrix.of x))]
        simp only [map_sub, map_mul, Complex.conj_conj]
        ring
      rw [integral_congr_ae hval, integral_const_mul, integral_conj,
        integral_sub (hg0.const_mul _) (hg1.const_mul _), integral_const_mul, integral_const_mul, e0, e1]
      have hE : (starRingEnd ℂ) b0 * (⟪l (σ x0 w0), η0⟫_ℂ * ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ) -
          (starRingEnd ℂ) b1 * (⟪l (σ x1 w0), η1⟫_ℂ * ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ) = 0 := by
        linear_combination ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ * hb
      rw [hE, map_zero, mul_zero]
    have hsplit : ∫ g, F g ∂μG = b0 * ∫ g, Φ0 g ∂μG - b1 * ∫ g, Φ1 g ∂μG := by
      show ∫ g, (b0 * Φ0 g - b1 * Φ1 g) ∂μG = _
      rw [integral_sub (hi0.const_mul b0) (hi1.const_mul b1), integral_const_mul, integral_const_mul]
    rw [hsplit, he0, he1] at hF0
    exact sub_eq_zero.mp hF0
  by_cases hzero : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ x w0) = 0
  · refine ⟨0, fun x0 hx0 => ?_⟩
    rw [zero_smul]
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right]
    have := comb x0 hx0 x0 hx0 η 0 1 0 (by rw [hzero x0 hx0]; simp)
    simpa using this
  · push_neg at hzero
    obtain ⟨x1, hx1, hl1⟩ := hzero
    have hy : ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hl1
    refine ⟨⟪l (σ x1 w0), W x1⟫_ℂ / ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ, fun x0 hx0 => ?_⟩
    apply ext_inner_left ℂ
    intro η
    rw [inner_smul_right]
    have hc := comb x0 hx0 x1 hx1 η (l (σ x1 w0)) ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ ⟪η, l (σ x0 w0)⟫_ℂ
      (by rw [inner_conj_symm, inner_conj_symm]; ring)
    rw [div_mul_eq_mul_div, eq_div_iff hy]
    linear_combination hc

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem besselOfW_of_local_decomposition (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := Formalism.FourierDecayAlt.P.discrete_series_form_one (Formalism.MainNotions.BridgeCS3dClosed.inputs_of hDI hJ)
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem besselOfW_of_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.SG.LocWSOf.BesselOfW :=
  besselOfW_of_local_decomposition Formalism.L2.SG.BesselDiscreteSeries.decInf hJ

end Formalism.MainNotions.BridgeCS3dBOW
