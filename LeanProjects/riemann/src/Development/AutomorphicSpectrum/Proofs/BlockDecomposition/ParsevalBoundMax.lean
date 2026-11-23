import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeNormCatRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableCatPhase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfMulBlk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeEqIntegralGau
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProfileIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualFWeightLe

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval.Max

theorem fz_decay2 (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
  classical
  have key : ∀ j : Fin 2, ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
      (1 + ‖A‖) ^ N * (|ξ j| ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
    intro j
    obtain ⟨Ψ₁, h₁⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Φ j
    obtain ⟨Ψ₂, h₂⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Ψ₁ j
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Ψ₂ N
    refine ⟨C, fun A ξ => ?_⟩
    have e : ‖fz Ψ₂ A ξ‖ = (2 * Real.pi * |ξ j|) ^ 2 * ‖fz Φ A ξ‖ := by
      rw [h₂, h₁, norm_mul, norm_mul]
      have : ‖-(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ))‖ = 2 * Real.pi * |ξ j| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]; ring
    have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
    refine le_trans ?_ (hC A ξ)
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [e, mul_pow]
    have : 0 ≤ |ξ j| ^ 2 * ‖fz Φ A ξ‖ := by positivity
    nlinarith
  obtain ⟨C₀, h₀⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Φ N
  obtain ⟨C₁, h₁⟩ := key 0
  obtain ⟨C₂, h₂⟩ := key 1
  refine ⟨2 * (C₀ + C₁ + C₂) + 0, fun A ξ => ?_⟩
  have hx : ‖ξ‖ ^ 2 ≤ |ξ 0| ^ 2 + |ξ 1| ^ 2 := by
    have hn : ‖ξ‖ ≤ max |ξ 0| |ξ 1| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      fin_cases i
      · simpa using le_max_left _ _
      · simpa using le_max_right _ _
    have h2 : ‖ξ‖ ^ 2 ≤ (max |ξ 0| |ξ 1|) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    refine h2.trans ?_
    rcases max_cases |ξ 0| |ξ 1| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg |ξ 0|, sq_nonneg |ξ 1|]
  have hsq : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2) := by
    nlinarith [sq_nonneg (‖ξ‖ - 1)]
  have hf : 0 ≤ ‖fz Φ A ξ‖ := norm_nonneg _
  have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
  have s := h₀ A ξ
  have s1 := h₁ A ξ
  have s2 := h₂ A ξ
  calc (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖)
      ≤ (1 + ‖A‖) ^ N * ((2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2)) * ‖fz Φ A ξ‖) := by gcongr
    _ = 2 * ((1 + ‖A‖) ^ N * ‖fz Φ A ξ‖ + (1 + ‖A‖) ^ N * (|ξ 0| ^ 2 * ‖fz Φ A ξ‖)
          + (1 + ‖A‖) ^ N * (|ξ 1| ^ 2 * ‖fz Φ A ξ‖)) := by ring
    _ ≤ 2 * (C₀ + C₁ + C₂) + 0 := by linarith

theorem parseval_bound_max (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
    (Matrix.of h).det ≠ 0 →
    ‖Ae Φ ε h v‖ ≤ C * ((max |(Matrix.of h).det|
      (|h 0 0 * h 0 1 + h 1 0 * h 1 1| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2)))⁻¹ / (1 + ‖h‖) ^ N) := by
  obtain ⟨C₁, hC₁⟩ := fz_decay2 Φ N
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CompanionTheory.Parseval.OneDim.wt_gau_bound
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0 0)
  set K : ℝ := max C₂ 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨C₁ * (1 + 4 * K), fun ε hε _ h v hdet => ?_⟩
  set D : ℝ := |(Matrix.of h).det| with hD
  have hD0 : 0 < D := abs_pos.2 hdet
  set S : ℝ := h 0 0 * h 0 1 + h 1 0 * h 1 1 with hSdef
  set m : ℝ := h 0 1 ^ 2 + h 1 1 ^ 2 with hm
  have hm0 : 0 < m := by
    have : m ≠ 0 := by
      intro h0
      have a1 : h 0 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      have a2 : h 1 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      apply hdet
      simp [Matrix.det_fin_two, a1, a2]
    exact lt_of_le_of_ne (by positivity) this.symm
  set n : ℝ := Real.sqrt m with hn
  have hn0 : 0 < n := Real.sqrt_pos.2 hm0
  have hnn : n * n = m := Real.mul_self_sqrt hm0.le
  set P : ℝ := (1 + ‖h‖) ^ N with hP
  have hP0 : 0 < P := by positivity
  set a : ℝ := D / n with ha
  have ha0 : 0 < a := div_pos hD0 hn0
  set l : ℝ := S / m with hl
  have hg : ∀ ζ, ‖gz Φ h ζ‖ ≤ D⁻¹ * C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
    intro ζ
    rw [GlobalTheory.CompanionTheory.Parseval.gz_eq_fz Φ h ζ hdet, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hD0.le)]
    have := hC₁ h (dualF h ζ)
    have hq : 0 < (1 + ‖dualF h ζ‖) ^ 2 := by positivity
    have h3 : ‖fz Φ h (dualF h ζ)‖ ≤ C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hP0, ← div_eq_mul_inv, le_div_iff₀ hq]
      calc _ = P * ((1 + ‖dualF h ζ‖) ^ 2 * ‖fz Φ h (dualF h ζ)‖) := by ring
        _ ≤ C₁ := this
    calc D⁻¹ * ‖fz Φ h (dualF h ζ)‖ ≤ D⁻¹ * (C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  set B : ℝ := D⁻¹ * C₁ / P with hB
  have hB0 : 0 ≤ B := by positivity
  have hnormI : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ = gau ε ζ * ‖gz Φ h ζ‖ := by
    intro ζ
    have : ‖Ad3.psiR (ζ * v)‖ = 1 := by
      unfold Ad3.psiR
      have : (-2 * (Real.pi : ℂ) * Complex.I * ((ζ * v : ℝ) : ℂ)) = ((-2 * Real.pi * (ζ * v) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (gau_nonneg ε ζ hε)]
    ring
  have b1 : ‖Ae Φ ε h v‖ ≤ B := by
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ gau ε ζ * B := by
      intro ζ
      rw [hnormI]
      refine mul_le_mul_of_nonneg_left ((hg ζ).trans ?_) (gau_nonneg ε ζ hε)
      have hi : ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        have : 0 ≤ ‖dualF h ζ‖ := norm_nonneg _
        nlinarith
      nlinarith
    refine (norm_integral_le_of_norm_le ((gau_integrable ε hε).mul_const B) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_mul_const, gau_integral ε hε, one_mul]
  have b2 : S ≠ 0 → ‖Ae Φ ε h v‖ ≤ 4 * K * B * (a / |l|) := by
    intro hS
    have hl0 : l ≠ 0 := div_ne_zero hS hm0.ne'
    have hwm : Measurable (wt a l) := by
      unfold wt
      fun_prop
    have hwi : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
      refine (gau_integrable ε hε).bdd_mul (c := 1) hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_of_nonneg (wt_nonneg _ _ _)]
      apply inv_le_one_of_one_le₀
      have : 0 ≤ |ζ - l| / a := by positivity
      nlinarith
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ (4 * B) * (wt a l ζ * gau ε ζ) := by
      intro ζ
      rw [hnormI]
      have g1 := GlobalTheory.CompanionTheory.Parseval.dualF_weight_le h ζ hdet
      have g2 : ‖gz Φ h ζ‖ ≤ B * (4 * wt a l ζ) :=
        (hg ζ).trans (mul_le_mul_of_nonneg_left g1 hB0)
      calc gau ε ζ * ‖gz Φ h ζ‖ ≤ gau ε ζ * (B * (4 * wt a l ζ)) :=
            mul_le_mul_of_nonneg_left g2 (gau_nonneg ε ζ hε)
        _ = _ := by ring
    refine (norm_integral_le_of_norm_le (hwi.const_mul (4 * B)) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_const_mul]
    have o := hC₂ ε a l hε ha0 hl0
    have o2 : ∫ ζ, wt a l ζ * gau ε ζ ≤ K * (a / |l|) :=
      o.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc 4 * B * ∫ ζ, wt a l ζ * gau ε ζ ≤ 4 * B * (K * (a / |l|)) :=
          mul_le_mul_of_nonneg_left o2 (by positivity)
      _ = _ := by ring
  have e1 : B = C₁ / P * D⁻¹ := by rw [hB]; ring
  have goal2 : C₁ * (1 + 4 * K) * ((max D (|S| / n))⁻¹ / P) = (C₁ / P) * (1 + 4 * K) * (max D (|S| / n))⁻¹ := by
    ring
  rw [goal2]
  have hQ : 0 ≤ C₁ / P := by positivity
  rcases le_total (|S| / n) D with hle | hle
  · rw [max_eq_left hle]
    calc ‖Ae Φ ε h v‖ ≤ C₁ / P * D⁻¹ := by rw [← e1]; exact b1
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * D⁻¹ * (4 * K) := by positivity
        nlinarith
  · rw [max_eq_right hle]
    have hSpos : 0 < |S| / n := lt_of_lt_of_le hD0 hle
    have hS : S ≠ 0 := by
      intro h0; rw [h0, abs_zero, zero_div] at hSpos; exact lt_irrefl _ hSpos
    have hS' : |S| ≠ 0 := abs_ne_zero.2 hS
    have hal : a / |l| = D * (n / |S|) := by
      rw [ha, hl, abs_div, abs_of_pos hm0, ← hnn]
      field_simp
    have e2 : 4 * K * B * (a / |l|) = 4 * K * (C₁ / P) * (n / |S|) := by
      rw [hal, hB]; field_simp
    rw [inv_div]
    calc ‖Ae Φ ε h v‖ ≤ 4 * K * (C₁ / P) * (n / |S|) := by rw [← e2]; exact b2 hS
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * (n / |S|) := by positivity
        nlinarith

end GlobalTheory.CompanionTheory.Parseval.Max
