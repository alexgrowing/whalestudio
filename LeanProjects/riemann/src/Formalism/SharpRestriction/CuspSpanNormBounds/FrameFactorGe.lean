import Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {r : ℕ} {κ τ : ℝ}

theorem frame_factor_ge (hκ : 0 < κ) (hτ : 0 < τ) (A A₁ : (Fin r → ℂ) × ℂ → ENNReal) (K F : ℝ) (hK : 0 < K)
    (hF : 0 ≤ F)
    (h1 : ∀ p, A₁ (sBig r κ τ p) ≤ ENNReal.ofReal (K * F) * A p)
    (h2 : ∀ p, ENNReal.ofReal K * A p ≤ ENNReal.ofReal F * A₁ (sBig r κ τ p))
    (hint : ∫⁻ p, A₁ p = ENNReal.ofReal K * ∫⁻ p, A p) (h0 : ∫⁻ p, A p ≠ 0) (htop : ∫⁻ p, A p ≠ ⊤) :
    jacBig r κ τ ≤ F ∧ 1 ≤ jacBig r κ τ * F := by
  have hJ := jacBig_pos (r := r) hκ hτ
  have hS := lintegral_sBig (r := r) hκ hτ A₁
  set I := ∫⁻ p, A p
  set I₁ := ∫⁻ p, A₁ (sBig r κ τ p)
  have e : ENNReal.ofReal (jacBig r κ τ) * I₁ = ENNReal.ofReal K * I := by rw [← hS, hint]
  have a1 : I₁ ≤ ENNReal.ofReal (K * F) * I := by
    calc I₁ ≤ ∫⁻ p, ENNReal.ofReal (K * F) * A p := lintegral_mono h1
      _ = ENNReal.ofReal (K * F) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have a2 : ENNReal.ofReal K * I ≤ ENNReal.ofReal F * I₁ := by
    calc ENNReal.ofReal K * I = ∫⁻ p, ENNReal.ofReal K * A p := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal F * A₁ (sBig r κ τ p) := lintegral_mono h2
      _ = ENNReal.ofReal F * I₁ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  constructor
  ·
    have b : ENNReal.ofReal (jacBig r κ τ * K) * I ≤ ENNReal.ofReal (F * K) * I := by
      calc ENNReal.ofReal (jacBig r κ τ * K) * I = ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal K * I) := by
            rw [ENNReal.ofReal_mul hJ.le, mul_assoc]
        _ ≤ ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal F * I₁) := by gcongr
        _ = ENNReal.ofReal F * (ENNReal.ofReal K * I) := by rw [mul_left_comm, e]
        _ = ENNReal.ofReal (F * K) * I := by rw [ENNReal.ofReal_mul hF, mul_assoc]
    have c := (ENNReal.mul_le_mul_iff_left h0 htop).mp b
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hF hK.le)] at c
    nlinarith
  · have b : ENNReal.ofReal K * I ≤ ENNReal.ofReal (jacBig r κ τ * K * F) * I := by
      calc ENNReal.ofReal K * I = ENNReal.ofReal (jacBig r κ τ) * I₁ := e.symm
        _ ≤ ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal (K * F) * I) := by gcongr
        _ = ENNReal.ofReal (jacBig r κ τ * K * F) * I := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hJ.le, mul_assoc (jacBig r κ τ)]
    have c := (ENNReal.mul_le_mul_iff_left h0 htop).mp b
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at c
    nlinarith

theorem jacBig_one (τ : ℝ) : jacBig r 1 τ = τ ^ (4 * (r + 1)) := by
  unfold jacBig tF
  simp only [one_pow, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]; ring_nf

theorem cf_ge_two (hτ : 1 < τ) (Cf : ℝ) (A A₁ : (Fin r → ℂ) × ℂ → ENNReal) (K : ℝ) (hK : 0 < K)
    (h1 : ∀ p, A₁ (sBig r 1 τ p) ≤
      ENNReal.ofReal (K * (max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)))) * A p)
    (h2 : ∀ p, ENNReal.ofReal K * A p ≤
      ENNReal.ofReal (max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ))) * A₁ (sBig r 1 τ p))
    (hint : ∫⁻ p, A₁ p = ENNReal.ofReal K * ∫⁻ p, A p) (h0 : ∫⁻ p, A p ≠ 0) (htop : ∫⁻ p, A p ≠ ⊤) :
    2 ≤ Cf := by
  have hτ0 : 0 < τ := by linarith
  have hmax : max τ τ⁻¹ = τ := max_eq_left (by
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ
    linarith)
  rw [hmax] at h1 h2
  have hF : 0 ≤ τ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hτ0.le _
  have := (frame_factor_ge one_pos hτ0 A A₁ K _ hK hF h1 h2 hint h0 htop).1
  rw [jacBig_one, ← Real.rpow_natCast] at this
  have h := (Real.rpow_le_rpow_left_iff hτ).mp this
  push_cast at h
  have hr : (0 : ℝ) < 2 * r + 2 := by positivity
  nlinarith

theorem frames_ineqs {pw pw₁ s K ρ F : ℝ} (X : ENNReal) (hs : 0 ≤ s) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (h1 : ρ ≤ F) (h2 : ρ⁻¹ ≤ F) (he : pw₁ * s = K * ρ * pw) :
    ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X) ≤ ENNReal.ofReal (K * F) * (ENNReal.ofReal pw * X) ∧
      ENNReal.ofReal K * (ENNReal.ofReal pw * X) ≤ ENNReal.ofReal F * (ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X)) := by
  have hF : 0 < F := lt_of_lt_of_le hρ h1
  rw [← mul_assoc (ENNReal.ofReal pw₁), ← ENNReal.ofReal_mul' hs, he]
  by_cases hp : pw ≤ 0
  · have h0 : K * ρ * pw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hρ.le) hp
    rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos hp]
    simp
  · push Not at hp
    constructor
    · rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK hF.le)]
      gcongr ENNReal.ofReal ?_ * _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hp.le
    · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hF.le]
      gcongr ENNReal.ofReal ?_ * _
      have : 1 ≤ F * ρ := by
        have := mul_le_mul_of_nonneg_right h2 hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at this
      nlinarith [mul_nonneg hK hp.le]

end Formalism.MainNotions.FrameBoundFromBesselTorus
