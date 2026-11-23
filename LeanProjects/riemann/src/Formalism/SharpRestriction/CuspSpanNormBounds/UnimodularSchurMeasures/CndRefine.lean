import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

theorem cnd_refine (C : ℝ) (hC : 1 ≤ C) (n q f : ℕ) (hq : 1 ≤ q) (hf : 1 ≤ f)
    (rd g b τ₁ D volK Kxx : ℝ) (hrd : 1 ≤ rd) (hg : 1 ≤ g) (hτ : 0 < τ₁) (hτ2 : τ₁ < 1 / 2) (hD : 0 ≤ D)
    (hvK : 0 < volK) (a : ℕ) (τ : ℕ → ℝ) (ha : 1 ≤ a) (haq : a ≤ q) (hpos : ∀ i, 0 < τ i)
    (htop : τ (a + 1) = 1 / 2) (h1 : τ 1 = τ₁)
    (H : ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
      ρ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧ Kxx ≤ s 0 ^ 2 ∧
      (∀ P < P0 n q f, s P ≤ ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * (b ^ 2 + (P : ℝ) * (n : ℝ))) * s (P + 1)) ∧
      s (P0 n q f) ^ 2 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * mult * (D / volK) ∧
      mult ≤ (C * Real.sqrt (n : ℝ) / τ₁ ^ 2) ^ (2 * n ^ 2 * f)) :
    ∃ ρ Bs : ℝ, 0 ≤ ρ ∧ ρ ≤ (4 * C) * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) ∧
      Kxx ≤ ((4 * C) * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b) ^ (2 * P0 n q f) * Bs ∧
      Bs ≤ D * volK⁻¹ * ((4 * C) * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * ((4 * C) / τ₁) ^ (4 * n ^ 2 * f) := by
  obtain ⟨b', hb1, hb2, hr⟩ := Formalism.HermitianLatticeCounting.Final.S7.gapPigeonhole a q τ ha haq hpos htop (h1 ▸ hτ2)
  obtain ⟨ρ, s, mult, h0, hρ, hs, hK, hstep, hB, hm⟩ := H b' hb1 hb2
  rw [h1] at hr
  have hC0 : 0 ≤ C := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hrd0 : 0 ≤ rd := by linarith
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb₁ : 0 ≤ b1 n q f b := by
    unfold Formalism.HermitianLatticeCounting.S7.b1
    positivity
  refine ⟨ρ, s (P0 n q f) ^ 2, h0, ?_, ?_, ?_⟩
  · have hco : 0 ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd := by positivity
    have hpw : 0 ≤ (2 * τ₁) ^ (1 / (q : ℝ)) := Real.rpow_nonneg (by linarith) _
    calc ρ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (τ b' / τ (b' + 1)) := hρ
      _ ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := mul_le_mul_of_nonneg_left hr hco
      _ ≤ (4 * C) * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := by
          have : 0 ≤ C * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) := mul_nonneg hco hpw
          nlinarith
  · have hsq : Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) ≤ (n : ℝ) * (f : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (n : ℝ) ^ 2 * (f : ℝ) * 1 ≤ (n : ℝ) ^ 2 * (f : ℝ) * (f : ℝ) :=
        mul_le_mul_of_nonneg_left hfR (by positivity)
      nlinarith
    have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) := Real.sqrt_nonneg _
    set Θ : ℝ := ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * b1 n q f b) with hΘ
    have hΘ0 : 0 ≤ Θ := by positivity
    have hit := Formalism.HermitianLatticeCounting.Final.S7.iterSup s
      (fun P => ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) * (C * (n : ℝ) * (b ^ 2 + (P : ℝ) * (n : ℝ)))) Θ (P0 n q f)
      (fun P hP => ⟨by positivity, by
        have h2 := (Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.stepsRoom n q f P b hq).2 (by omega)
        have hc : 0 ≤ ρ * Real.sqrt ((n : ℝ) ^ 2 * (f : ℝ)) := by positivity
        have hc2 : 0 ≤ C * (n : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hc2) hc⟩) hs hstep
    have hΘle : Θ ≤ (4 * C) * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b := by
      have e1 : Θ ≤ ρ * ((n : ℝ) * (f : ℝ)) * (C * (n : ℝ) * b1 n q f b) := by
        rw [hΘ]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq h0) (by positivity)
      have e2 : 0 ≤ C * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b := by positivity
      nlinarith
    have hs0 : s 0 ^ 2 ≤ (Θ ^ P0 n q f * s (P0 n q f)) ^ 2 := pow_le_pow_left₀ (hs 0) hit 2
    calc Kxx ≤ s 0 ^ 2 := hK
      _ ≤ (Θ ^ P0 n q f * s (P0 n q f)) ^ 2 := hs0
      _ = Θ ^ (2 * P0 n q f) * s (P0 n q f) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm (P0 n q f) 2]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΘ0 hΘle _) (by positivity)
  · have hcm := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.cubeMult C n f (b1 n q f b) τ₁ hC hb₁ hτ
    have hDv : 0 ≤ D / volK := div_nonneg hD hvK.le
    have hfac : 0 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) :=
      pow_nonneg (div_nonneg (by norm_num) (div_nonneg zero_le_one (by positivity))) _
    calc s (P0 n q f) ^ 2 ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * mult * (D / volK) := hB
      _ ≤ (4 / (1 / (C * (n : ℝ) * b1 n q f b))) ^ (n ^ 2 * f) * (C * Real.sqrt (n : ℝ) / τ₁ ^ 2) ^ (2 * n ^ 2 * f) *
            (D / volK) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hDv
      _ ≤ (4 * C * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (4 * C / τ₁) ^ (4 * n ^ 2 * f) * (D / volK) :=
          mul_le_mul_of_nonneg_right hcm hDv
      _ = _ := by rw [div_eq_mul_inv]; ring

def CSize.DeepStepsT {X : CData} (S : CSize X) (volK C : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      ∃ (a : ℕ) (τ : ℕ → ℝ), 1 ≤ a ∧ a ≤ X.qq ∧ (∀ i, 0 < τ i) ∧ τ (a + 1) = 1 / 2 ∧ τ 1 = S.tau1 x ∧
        ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
          ρ ≤ C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧
          |(X.kerD x).re| ≤ s 0 ^ 2 ∧
          (∀ P < P0 X.I.n X.qq X.I.f, s P ≤ ρ * Real.sqrt ((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
            (C * (X.I.n : ℝ) * (X.b ^ 2 + (P : ℝ) * (X.I.n : ℝ))) * s (P + 1)) ∧
          s (P0 X.I.n X.qq X.I.f) ^ 2 ≤ (4 / (1 / (C * (X.I.n : ℝ) * b1 X.I.n X.qq X.I.f X.b))) ^ (X.I.n ^ 2 * X.I.f) * mult *
            (X.Dc / volK) ∧
          mult ≤ (C * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

end Formalism.MainNotions.LeviCoordinates

end
