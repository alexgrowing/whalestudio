import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.ZetaVanish

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma isUnit_det_of_mem_Glev {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hg : g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) : IsUnit (Matrix.det g) := by
  have h1 : Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg.1
  have h2 : (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
    calc (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g
        = _root_.Formalism.QuantumDeterminants.Hpk k r * (Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact Matrix.isUnit_det_of_left_inverse h2

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma haar_isOpen_ne_zero_of_mem_Glev {k r : ℕ} {μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)}
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ) {V : Set (_root_.Formalism.QuantumDeterminants.Mt k r)} (hV : IsOpen V)
    {g₀ : _root_.Formalism.QuantumDeterminants.Mt k r} (hg₀ : Matrix.of g₀ ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (hgV : g₀ ∈ V) :
    μ V ≠ 0 := by
  intro h0
  have hnull : ∀ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), μ (_root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 := by
    intro a ha
    rw [← Measure.map_apply (_root_.Formalism.FourierDecayAlt.P.B2x5.measurable_lmulM a) hV.measurableSet, hμ.left a ha, h0]
  obtain ⟨t, hts, htc, hteq⟩ := TopologicalSpace.isOpen_biUnion_countable
    (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (fun a ↦ _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V)
    (fun a _ ↦ hV.preimage (_root_.Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM a))
  have hU : μ (⋃ a ∈ t, _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 :=
    (measure_biUnion_null_iff htc).2 fun a ha ↦ hnull a (hts ha)
  rw [hteq] at hU
  have hae : ∀ᵐ y ∂μ, y ∉ ⋃ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V :=
    measure_eq_zero_iff_ae_notMem.1 hU
  have hfalse : ∀ᵐ _y ∂μ, False := by
    filter_upwards [hae, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy hyU
    apply hy
    refine Set.mem_iUnion₂.2 ⟨Matrix.of g₀ * (Matrix.of y)⁻¹,
      _root_.Formalism.FourierDecayAlt.P.Qx3.glev_mul hg₀ (_root_.Formalism.FourierDecayAlt.Q.TInvW.glev_inv hyU), ?_⟩
    show _root_.Formalism.QuantumDeterminants.lmulM _ y ∈ V
    unfold _root_.Formalism.QuantumDeterminants.lmulM
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_Glev hyU), Matrix.mul_one]
    exact hgV
  exact hμ.ne_zero (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma zetaFunction_vanish_of_orthogonal_bumps_lemma {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hz' : _root_.Formalism.QuantumDeterminants.inWb k r z') (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z) (hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z')
    (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (c : Fin r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ)
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ)
    (hcont : ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'})
    (hfib : ∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' →
      _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g' → h g = h g')
    (horth : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' < Complex.normSq ζ} →
      ∫ y : _root_.Formalism.QuantumDeterminants.Mt k r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta k r z z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0)
    (g₀ : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hg₀ : (c, g₀) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z') : h g₀ = 0 := by
  set TT := _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' with hTT
  set ζf : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ := _root_.Formalism.FourierDecayAlt.Q.zetaL k r z z' (Fin.last r) with hζf
  have hζc : Continuous ζf := (_root_.Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous
  have hzeta : ∀ g, _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = ζf g := fun g ↦ rfl
  have hH : ∀ g, _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g = Complex.normSq (ζf g) - TT := fun g ↦ rfl
  have hD : ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' ↔
      c ∈ _root_.Formalism.QuantumDeterminants.OmX r ∧ g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ 0 < _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g := fun g ↦ Iff.rfl
  obtain ⟨hc, hg₀G, hg₀H⟩ := (hD g₀).1 hg₀
  by_contra hw
  set w := h g₀ with hwdef
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ζ₀ := ζf g₀ with hζ₀
  set ε := (Complex.normSq ζ₀ - TT) / 2 with hε
  have hg₀H' : 0 < Complex.normSq ζ₀ - TT := by rw [hζ₀, ← hH]; exact hg₀H
  have hεpos : 0 < ε := by rw [hε]; linarith
  set R := ‖ζ₀‖ + 1 with hR
  set K := {g | g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ ε ≤ _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g ∧ ‖ζf g‖ ≤ R} with hKdef
  have hK : IsCompact K := _root_.Formalism.FourierDecayAlt.P5.HerB.isCompact_zeta_le z z' hz hz' hT hT' ε R
  have hKD : K ⊆ {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'} := fun g hg ↦
    (hD g).2 ⟨hc, hg.1, lt_of_lt_of_le hεpos hg.2.1⟩
  set K' := K ∩ h ⁻¹' {x | ‖w‖ / 2 ≤ ‖x - w‖} with hK'def
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    ((hcont.mono hKD).preimage_isClosed_of_isClosed hK.isClosed
      (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right w))))
    Set.inter_subset_left
  have hCc : IsCompact (ζf '' K') := hK'c.image hζc
  have hζ₀C : ζ₀ ∉ ζf '' K' := by
    rintro ⟨y, ⟨hyK, hyh⟩, hy⟩
    have hyw : h y = w := hfib y g₀ (hKD hyK) hg₀ (by rw [hzeta, hzeta, hy])
    have : ‖w‖ / 2 ≤ ‖h y - w‖ := hyh
    rw [hyw, sub_self, norm_zero] at this
    linarith
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hCc.isClosed.isOpen_compl ζ₀ hζ₀C
  set O := {ζ : ℂ | TT + ε < Complex.normSq ζ} ∩ {ζ | ‖ζ‖ < R} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt continuous_norm continuous_const)
  have hζ₀O : ζ₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · show TT + ε < Complex.normSq ζ₀
      rw [hε]; linarith
    · show ‖ζ₀‖ < R
      rw [hR]; linarith
  obtain ⟨ρ, hρ, hballO⟩ := Metric.isOpen_iff.1 hO ζ₀ hζ₀O
  set δ := min δ₁ ρ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hρ
  let b : ContDiffBump ζ₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hball : ∀ ζ, ζ ∈ tsupport b → ζ ∈ Metric.ball ζ₀ δ := by
    intro ζ hζ
    rw [b.tsupport_eq] at hζ
    exact Metric.closedBall_subset_ball (show δ / 2 < δ by linarith) hζ
  have hballC : Metric.ball ζ₀ δ ⊆ (ζf '' K')ᶜ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball₁
  have hballO' : Metric.ball ζ₀ δ ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hballO
  have hgood : ∀ g, g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) → b (ζf g) ≠ 0 →
      g ∈ K ∧ ‖h g - w‖ < ‖w‖ / 2 := by
    intro g hg hb
    have hmem : ζf g ∈ Metric.ball ζ₀ δ := hball _ (subset_tsupport _ hb)
    have hO' := hballO' hmem
    have h1 : TT + ε < Complex.normSq (ζf g) := hO'.1
    have h2 : ‖ζf g‖ < R := hO'.2
    have hgK : g ∈ K := ⟨hg, by rw [hH]; linarith, le_of_lt h2⟩
    refine ⟨hgK, ?_⟩
    by_contra hlt
    exact hballC hmem ⟨g, ⟨hgK, le_of_not_gt hlt⟩, rfl⟩
  have hre : ∀ g, ‖h g - w‖ < ‖w‖ / 2 → 0 < (star w * h g).re := by
    intro g hg
    have hsplit : (star w * h g).re = (star w * w).re + (star w * (h g - w)).re := by
      rw [← Complex.add_re, ← mul_add, add_sub_cancel]
    have hww : (star w * w).re = ‖w‖ ^ 2 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    have hlow : -(‖w‖ * ‖h g - w‖) ≤ (star w * (h g - w)).re := by
      have h3 := Complex.abs_re_le_norm (star w * (h g - w))
      rw [norm_mul, norm_star] at h3
      linarith [neg_abs_le (star w * (h g - w)).re]
    have h4 : ‖w‖ * ‖h g - w‖ ≤ ‖w‖ * (‖w‖ / 2) :=
      mul_le_mul_of_nonneg_left hg.le hwpos.le
    nlinarith
  have hof : Continuous (fun y : _root_.Formalism.QuantumDeterminants.Mt k r ↦ (Matrix.of y : _root_.Formalism.FourierDecayAlt.Q.Mx k r)) := continuous_id
  set F : _root_.Formalism.QuantumDeterminants.Mt k r → ℂ := fun y ↦ ((b (ζf (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) with hFdef
  have hint0 : ∫ y, F y ∂μ = 0 := horth b b.contDiff b.hasCompactSupport (fun ζ hζ ↦ by
    have h1 : TT + ε < Complex.normSq ζ := (hballO' (hball ζ hζ)).1
    show TT < Complex.normSq ζ
    linarith)
  set Kt : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ K} with hKtdef
  have hKt : IsCompact Kt := hK
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun S hS ↦ hμ.finite_compact S hS⟩
  have hFc : ContinuousOn F Kt :=
    (Complex.continuous_ofReal.comp (b.continuous.comp (hζc.comp hof))).continuousOn.mul
      ((hcont.mono hKD).comp hof.continuousOn fun y hy ↦ hy)
  have hIon : IntegrableOn F Kt μ := hFc.integrableOn_compact hKt
  have hae : F =ᵐ[μ] Kt.indicator F := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    by_cases hyK : y ∈ Kt
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK]
      have hb0 : b (ζf (Matrix.of y)) = 0 := by
        by_contra hb
        exact hyK (hgood _ hy hb).1
      simp [hFdef, hb0]
  have hFint : Integrable F μ :=
    ((integrable_indicator_iff hKt.measurableSet).2 hIon).congr hae.symm
  set f : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun y ↦ (star w * F y).re with hfdef
  have hfint : Integrable f μ := (hFint.const_mul (star w)).re
  have hfint0 : ∫ y, f y ∂μ = 0 := by
    have e := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hFint.const_mul (star w))
    simp only [Complex.reCLM_apply] at e
    rw [hfdef, e, integral_const_mul, hint0, mul_zero, Complex.zero_re]
  have hfval : ∀ y, f y = b (ζf (Matrix.of y)) * (star w * h (Matrix.of y)).re := by
    intro y
    simp only [hfdef, hFdef]
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have hfnn : 0 ≤ᵐ[μ] f := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    rw [Pi.zero_apply, hfval]
    by_cases hb : b (ζf (Matrix.of y)) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg (b.nonneg) (hre _ (hgood _ hy hb).2).le
  have hf0 : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hfnn hfint).1 hfint0
  set V : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | ζf (Matrix.of y) ∈ Metric.ball ζ₀ (δ / 4)} with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball.preimage (hζc.comp hof)
  have hg₀V : (g₀ : _root_.Formalism.QuantumDeterminants.Mt k r) ∈ V := Metric.mem_ball_self (by positivity)
  refine haar_isOpen_ne_zero_of_mem_Glev hμ hVo (g₀ := g₀) hg₀G hg₀V ?_
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hf0, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy0 hyG hyV
  have hb1 : b (ζf (Matrix.of y)) = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hyV)
  have hpos := hre _ (hgood _ hyG (by rw [hb1]; exact one_ne_zero)).2
  have : f y = 0 := hy0
  rw [hfval, hb1, one_mul] at this
  linarith

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.ZetaVanish.zeta_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt P.k P.r)) (c : Fin P.r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx P.k P.r → ℂ), _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev P.k P.r (Fin.last P.r)) μ → ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z'} → (∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g = _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g' → h g = h g') → (∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' < Complex.normSq ζ} → ∫ y : _root_.Formalism.QuantumDeterminants.Mt P.k P.r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0) → ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → h g = 0 := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ c h hμ hcont hfib horth g hg
  have hT : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z := by
    obtain ⟨⟩ := Bs
    assumption
  have hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' := by
    obtain ⟨⟩ := Bs
    assumption
  exact zetaFunction_vanish_of_orthogonal_bumps_lemma Bs.z_mem Bs.z'_mem hT hT' μ c h hμ hcont hfib horth g hg

end GlobalTheory.HatNF.ZetaVanish
