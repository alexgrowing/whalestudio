import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierBoundSeminormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeminormCompUnitaryLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWhittakerGL2LeIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralDecayProductLeRatioPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl2ComplexIwasawaDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableUnitNormPowDecayStatement

noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.AbsoluteW2Bounds

theorem pS_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) (f : SchwartzMap E ℂ) :
    0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem doubleOverlap_le_preimage_inter {C1 c e : ℝ} {N : ℕ} (hC1 : 0 ≤ C1) (hc : 0 ≤ c)
    (b1 : ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ), ‖sF f x ξ‖ ≤ C1 * pS N f * (dd x * dd ξ))
    (b5 : ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
      Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) ∧
      ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤ c * (‖A‖ / ‖D‖) ^ (-e))
    (k : ℕ) (f f' : SchwartzMap (Fin 2 → ℂ) ℂ) (κ : Matrix (Fin 2) (Fin 2) ℂ) (A B D : ℂ)
    (hA : A ≠ 0) (hD : D ≠ 0) (hκ : ‖κ.det‖ = 1) (hf : ∀ v, f' v = f (Matrix.vecMul v κ)) :
    ‖W2 k f (!![A, B; 0, D] * κ)‖ ≤ C1 * pS N f' * c * (‖A‖ / ‖D‖) ^ (1 - e) := by
  have hP : 0 ≤ pS N f' := pS_nonneg N f'
  have hr : 0 < ‖A‖ / ‖D‖ := div_pos (norm_pos_iff.2 hA) (norm_pos_iff.2 hD)
  obtain ⟨i5, l5⟩ := b5 A D hA hD
  have h3 := GlobalTheory.T.norm_whittakerGL2_le_integral k f f' κ A B D hA hD hκ hf
  have hint : ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ ≤
      C1 * pS N f' * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      (i5.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
    have := b1 f' (t * A) (t * D)⁻¹
    have h0 : 0 ≤ (‖t‖ ^ 2)⁻¹ := by positivity
    calc (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖
        ≤ (‖t‖ ^ 2)⁻¹ * (C1 * pS N f' * (dd (t * A) * dd (t * D)⁻¹)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hmul : 0 ≤ C1 * pS N f' := mul_nonneg hC1 hP
  calc ‖W2 k f (!![A, B; 0, D] * κ)‖
      ≤ ‖A‖ * ‖D‖⁻¹ * (C1 * pS N f' * (c * (‖A‖ / ‖D‖) ^ (-e))) := by
        refine h3.trans (mul_le_mul_of_nonneg_left (hint.trans ?_) (by positivity))
        exact mul_le_mul_of_nonneg_left l5 hmul
    _ = C1 * pS N f' * c * ((‖A‖ / ‖D‖) * (‖A‖ / ‖D‖) ^ (-e)) := by
        rw [div_eq_mul_inv ‖A‖ ‖D‖]; ring
    _ = _ := by
        rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]

theorem two_bounds {X K1 K2 s σ : ℝ} (hs : 0 < s) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (b1 : X ≤ K1 * s ^ σ) (b2 : X ≤ K2 * s ^ (σ - 1)) :
    X ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹ + s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by
  have hp : 0 < s ^ σ := Real.rpow_pos_of_pos hs _
  have hq : 0 < s ^ (σ + 1) := Real.rpow_pos_of_pos hs _
  have hi : 0 < (1 + s ^ 2)⁻¹ := by positivity
  rcases le_total s 1 with hs1 | hs1
  · have hd : (1 : ℝ) ≤ 2 * (1 + s ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      nlinarith
    have e1 : K1 * s ^ σ ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹) := by
      have : s ^ σ ≤ s ^ σ * (2 * (1 + s ^ 2)⁻¹) := le_mul_of_one_le_right hp.le hd
      calc K1 * s ^ σ ≤ K1 * (s ^ σ * (2 * (1 + s ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left this h1
        _ = 2 * K1 * (s ^ σ * (1 + s ^ 2)⁻¹) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : 0 ≤ 2 * (K1 + K2) * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by positivity
    linarith
  · have e : s ^ (σ - 1) = s ^ (σ + 1) * (s ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
      congr 1
      push_cast
      ring
    have hd2 : (s ^ 2)⁻¹ ≤ 2 * (1 + s ^ 2)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e2 : K2 * s ^ (σ - 1) ≤ 2 * (K1 + K2) * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by
      rw [e]
      calc K2 * (s ^ (σ + 1) * (s ^ 2)⁻¹)
          ≤ K2 * (s ^ (σ + 1) * (2 * (1 + s ^ 2)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd2 hq.le) h2
        _ = 2 * K2 * (s ^ (σ + 1) * (1 + s ^ 2)⁻¹) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e3 : 0 ≤ 2 * (K1 + K2) * (s ^ σ * (1 + s ^ 2)⁻¹) := by positivity
    linarith

theorem main : Ad3.K.LC.C.AbsoluteZetaIntegralBound := by
  intro k hk σ h0 h1
  obtain ⟨C1, N, hC1, b1⟩ := GlobalTheory.T.partial_fourier_bound_seminorm
  obtain ⟨C2, hC2, b2⟩ := GlobalTheory.T.seminorm_comp_unitary_le N
  obtain ⟨c1, hc1, b5⟩ := GlobalTheory.T.integral_decay_product_le_ratio_pow σ h0 (by linarith)
  obtain ⟨c2, hc2, b6⟩ := GlobalTheory.T.integral_decay_product_le_ratio_pow (σ + 1) (by linarith) (by linarith)
  have hI := GlobalTheory.T.integrable_unit_norm_pow_decay σ h0 h1
  set M : ℂˣ → ℝ := fun a => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a with hM
  have hM0 : ∀ a, 0 ≤ M a := fun a => by
    have := dd_pos (a : ℂ)
    simp only [hM]
    positivity
  have hJ : 0 ≤ ∫ a, M a ∂mulC := integral_nonneg hM0
  refine ⟨2 * (C1 * C2 * c1 + C1 * C2 * c2) * ∫ a, M a ∂mulC, N, fun f g hg => ?_⟩
  obtain ⟨κ, b, R, hR, hR2, hκ, hκd, hgκ⟩ := GlobalTheory.T.gl2_complex_iwasawa_decomposition_upper_unitary g hg
  obtain ⟨f', hf', hP⟩ := b2 κ hκ f
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  set y : ℂ := g.det / (R : ℂ) ^ 2 with hy
  have hy0 : y ≠ 0 := div_ne_zero hg (pow_ne_zero _ hRc)
  set yu : ℂˣ := Units.mk0 y hy0 with hyu
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hf0 : 0 ≤ pS N f := pS_nonneg N f
  have hf1 : 0 ≤ pS N f' := pS_nonneg N f'
  set Q : ℝ := pS N f with hQ
  have hpt : ∀ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤
      (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * M (yu * a) := by
    intro a
    have ha : (a : ℂ) ≠ 0 := a.ne_zero
    have han : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 ha
    set s : ℝ := ‖y * (a : ℂ)‖ with hs
    have hs0 : 0 < s := norm_pos_iff.2 (mul_ne_zero hy0 ha)
    have hmat : d2 a * g = !![(a : ℂ) * (g.det / (R : ℂ)), (a : ℂ) * b; 0, (R : ℂ)] * κ := by
      conv_lhs => rw [hgκ]
      rw [← Matrix.mul_assoc]
      congr 1
      simp [d2, Matrix.mul_fin_two]
    have hA : (a : ℂ) * (g.det / (R : ℂ)) ≠ 0 := mul_ne_zero ha (div_ne_zero hg hRc)
    have hr : ‖(a : ℂ) * (g.det / (R : ℂ))‖ / ‖(R : ℂ)‖ = s := by
      have e : y * (a : ℂ) = (a : ℂ) * (g.det / (R : ℂ)) / (R : ℂ) := by
        rw [hy]; field_simp
      rw [hs, e, norm_div]
    have w1 := doubleOverlap_le_preimage_inter hC1 hc1 b1 (b5) k f f' κ _ ((a : ℂ) * b) _ hA hRc hκd hf'
    have w2 := doubleOverlap_le_preimage_inter hC1 hc2 b1 (b6) k f f' κ _ ((a : ℂ) * b) _ hA hRc hκd hf'
    rw [← hmat, hr] at w1 w2
    have hpow : ‖(a : ℂ)‖ ^ (2 * σ - 1) = ‖y‖ ^ (1 - 2 * σ) * s ^ (2 * σ - 1) := by
      have : s = ‖y‖ * ‖(a : ℂ)‖ := by rw [hs, norm_mul]
      rw [this, Real.mul_rpow hyn.le han.le, ← mul_assoc, ← Real.rpow_add hyn]
      simp
    set Y : ℝ := ‖y‖ ^ (1 - 2 * σ) with hY
    have hY0 : 0 < Y := Real.rpow_pos_of_pos hyn _
    have hPQ : C1 * pS N f' ≤ C1 * (C2 * Q) := mul_le_mul_of_nonneg_left hP hC1
    have hp2 : 0 ≤ s ^ (2 * σ - 1) := (Real.rpow_pos_of_pos hs0 _).le
    have u1 : ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤ (C1 * C2 * c1 * Q * Y) * s ^ σ := by
      rw [hpow]
      have e : s ^ σ = s ^ (1 - σ) * s ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      have w1' : ‖W2 k f (d2 a * g)‖ ≤ C1 * (C2 * Q) * c1 * s ^ (1 - σ) := by
        refine w1.trans ?_
        have : 0 ≤ s ^ (1 - σ) := (Real.rpow_pos_of_pos hs0 _).le
        gcongr
      calc ‖W2 k f (d2 a * g)‖ * (Y * s ^ (2 * σ - 1))
          ≤ (C1 * (C2 * Q) * c1 * s ^ (1 - σ)) * (Y * s ^ (2 * σ - 1)) :=
            mul_le_mul_of_nonneg_right w1' (by positivity)
        _ = _ := by rw [e]; ring
    have u2 : ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ≤
        (C1 * C2 * c2 * Q * Y) * s ^ (σ - 1) := by
      rw [hpow]
      have e : s ^ (σ - 1) = s ^ (1 - (σ + 1)) * s ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      have w2' : ‖W2 k f (d2 a * g)‖ ≤ C1 * (C2 * Q) * c2 * s ^ (1 - (σ + 1)) := by
        refine w2.trans ?_
        have : 0 ≤ s ^ (1 - (σ + 1)) := (Real.rpow_pos_of_pos hs0 _).le
        gcongr
      calc ‖W2 k f (d2 a * g)‖ * (Y * s ^ (2 * σ - 1))
          ≤ (C1 * (C2 * Q) * c2 * s ^ (1 - (σ + 1))) * (Y * s ^ (2 * σ - 1)) :=
            mul_le_mul_of_nonneg_right w2' (by positivity)
        _ = _ := by rw [e]; ring
    have hfin := two_bounds hs0 (K1 := C1 * C2 * c1 * Q * Y) (K2 := C1 * C2 * c2 * Q * Y)
      (by positivity) (by positivity) u1 u2
    have hMe : M (yu * a) = s ^ σ * (1 + s ^ 2)⁻¹ + s ^ (σ + 1) * (1 + s ^ 2)⁻¹ := by
      simp [hM, hyu, dd, hs]
    rw [hMe]
    refine hfin.trans (le_of_eq ?_)
    ring
  have hIy : Integrable (fun a : ℂˣ => M (yu * a)) mulC := hI.comp_mul_left yu
  have hmeas : AEStronglyMeasurable
      (fun a : ℂˣ => ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1)) mulC := by
    refine (GlobalTheory.T.aestronglyMeasurable_whittaker_diag_units k f g).norm.mul ?_
    have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
    exact (hv.norm.pow_const _).aestronglyMeasurable
  have hnn : ∀ a : ℂˣ, 0 ≤ ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) := fun a => by positivity
  have hdom := hIy.const_mul (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ))
  refine ⟨hdom.mono' hmeas (Filter.Eventually.of_forall fun a => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn a)]
    exact hpt a
  · have hY : Yb g ^ (1 / 2 - σ) = ‖y‖ ^ (1 - 2 * σ) := by
      have e : Yb g = ‖y‖ ^ 2 := by
        rw [Yb, ← hR2, hy, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
        field_simp
      rw [e, ← Real.rpow_natCast, ← Real.rpow_mul hyn.le]
      congr 1
      push_cast
      ring
    calc ∫ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ∂mulC
        ≤ ∫ a : ℂˣ, (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * M (yu * a) ∂mulC :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hdom
            (Filter.Eventually.of_forall hpt)
      _ = (2 * (C1 * C2 * c1 + C1 * C2 * c2) * Q * ‖y‖ ^ (1 - 2 * σ)) * ∫ a, M a ∂mulC := by
          rw [integral_const_mul, integral_mul_left_eq_self M yu]
      _ = _ := by rw [hY]; ring

end GlobalTheory.CompanionTheory.AbsoluteW2Bounds
