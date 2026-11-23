import Mathlib
import Formalism.GL3MeanSquares.InvNormSqConjRatioPowIdentities
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.HadamardUnitDiagonalDetLeOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.GlobalBoundRefinements

section ShortIntervalLowerBound

open Formalism.HermitianLattices.GL2PrimeSums

open private gl2a4_root gl2a4_rho_pos gl2a4_rho_mono gl2a4_weight gl2a4_E_lower gl2a4_E_upper Li_le_three_mul_div_log
  gl2a4_Li_two gl2a4_Li_mono gl2a4_E_four gl2a4_E_nonneg Emain_lower_bound from Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound

private lemma exists_adjusted_exceptional_exponent {cb B β X : ℝ} {θ : ℤ} (hcb : 0 < cb) (hB : 4 ≤ B)
    (hβ : θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β)
    (hcbX : 2 / cb * Real.log B ≤ Real.log X) :
    ∃ β' : ℝ, 1 / 2 ≤ β' ∧ β' < 1 ∧
      (∀ Y, Emain θ β Y = Emain θ β' Y) ∧ (θ = 1 → 2 / B ^ 2 ≤ (1 - β') * Real.log X) := by
  by_cases hθ : θ = 0
  · refine ⟨1 / 2, by norm_num, by norm_num, fun Y => ?_, fun h1 => ?_⟩
    · simp only [Emain, hθ, Int.cast_zero, zero_mul, sub_zero]
    · exfalso
      omega
  · obtain ⟨h1, h2, h3⟩ := hβ hθ
    refine ⟨β, h1, h2, fun Y => rfl, fun _ => ?_⟩
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hBpos : 0 < B := by linarith
    have hcbne : cb ≠ 0 := hcb.ne'
    have hlogne : Real.log B ≠ 0 := hlogB.ne'
    have hBne : B ≠ 0 := hBpos.ne'
    have e : 2 / B ^ 2 = cb / (B ^ 2 * Real.log B) * (2 / cb * Real.log B) := by
      field_simp
      try ring
    rw [e]
    exact mul_le_mul h3 hcbX (mul_nonneg (div_nonneg (by norm_num) hcb.le) hlogB.le) (by linarith)

private lemma mul_log_le_log_of_rpow_le {B K X : ℝ} (hB : 4 ≤ B) (h : B ^ K ≤ X) : K * Real.log B ≤ Real.log X := by
  have hB0 : 0 < B := by linarith
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hB0 K) h
  rwa [Real.log_rpow hB0] at h1

set_option maxHeartbeats 1000000 in
private lemma exceptional_zero_contribution_bound {Cr cr B G β X : ℝ} {θ : ℤ} {π₁ π₂ : ℝ → ℕ} {η' : ℝ → ℝ} (hCr : 0 < Cr) (hcr : 0 < cr)
    (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) (hB : 4 ≤ B) (hG1 : 1 ≤ G) (hGB : G ≤ B)
    (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) (hd : θ = 1 → 2 / B ^ 2 ≤ (1 - β) * Real.log X)
    (hX : B ^ (60 : ℝ) ≤ X)
    (hπ₂ : ∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y)
    (hη : ∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B)
    (hQ : ∀ Y : ℝ, X ≤ Y →
      |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y)
    {h : ℝ} (hh1 : h ≤ 1) (hρ : rhoErr Cr cr B X ≤ h / 100) (hB7 : B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3)) :
    1 / 100 * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X := by
  obtain ⟨u, hu, hu12, hsq, hcb, hlogu⟩ := gl2a4_root hB hX
  have hB0 : 0 < B := by linarith
  have hu0 : 0 < u := by linarith
  have hX0 : 0 < X := by rw [← hu12]; positivity
  have hXu : u ≤ X := by
    have : u ^ 1 ≤ u ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith [pow_one u]
  have hXbig : 1296 ≤ X := by
    have h2 : u ^ 2 ≤ u ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hh0 : 0 < h := by linarith [gl2a4_rho_pos (c := cr) (B := B) (X := X) hCr]
  set X' := X * (1 + h) with hX'
  have hXX' : X ≤ X' := by rw [hX']; nlinarith
  have hX'2 : X' ≤ 2 * X := by rw [hX']; nlinarith
  have hX'sq : X' ≤ X ^ 2 := by nlinarith
  have hX'0 : 0 < X' := by linarith
  obtain ⟨W, hW1, hW2, hWlo, hWhi⟩ := gl2a4_weight hθ hβ2 (B := B) (Z := X) (by linarith) (by linarith)
    (by
      intro h
      have h1 := hd h
      have e : 2 / B ^ 2 = 2 * (1 / B ^ 2) := by ring
      have : 0 < 1 / B ^ 2 := by positivity
      rw [e] at h1
      linarith)
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW1
  have hLL' : Real.log X ≤ Real.log X' := Real.log_le_log hX0 hXX'
  have hL'0 : 0 < Real.log X' := by linarith
  have hL' : Real.log X' ≤ 2 * Real.log X := by
    have h1 : Real.log X' ≤ Real.log (X ^ 2) := Real.log_le_log hX'0 hX'sq
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  set L := Real.log X with hLdef
  set T := W * h * X / L with hT
  have hT0 : 0 < T := by rw [hT]; positivity

  have a1 := gl2a4_E_lower θ (β := β) (a := X) (b := X') (W := W) (by linarith) hX1 hXX' hW0.le
    (fun t ht _ => hWlo t ht)
  have a2 : T / 2 ≤ W * (X' - X) / Real.log X' := by
    have e1 : X' - X = h * X := by rw [hX']; ring
    have e2 : T / 2 = W * (h * X) / (2 * L) := by rw [hT]; field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) hL'0 hL'

  have b1 := gl2a4_E_upper θ (β := β) (a := 4) (b := X') (V := 2 * W) (by linarith) (by norm_num)
    (by linarith) (fun t ht1 ht2 => hWhi t (by linarith) (by linarith))
  have b2 : Li X' ≤ 3 * X' / Real.log X' := Li_le_three_mul_div_log (by linarith)
  have b3 : 3 * X' / Real.log X' ≤ 6 * X / L := by
    calc 3 * X' / Real.log X' ≤ 6 * X / Real.log X' :=
          div_le_div_of_nonneg_right (by linarith) hL'0.le
      _ ≤ 6 * X / L := div_le_div_of_nonneg_left (by positivity) hL hLL'
  have b4 : 0 ≤ Li 4 := by
    rw [← gl2a4_Li_two]; exact gl2a4_Li_mono (by norm_num) (by norm_num)
  have b5 : Emain θ β X' ≤ 6 + 12 * (W * X / L) := by
    have h1 : 2 * W * (Li X' - Li 4) ≤ 2 * W * (6 * X / L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e : 2 * W * (6 * X / L) = 12 * (W * X / L) := by ring
    have := (gl2a4_E_four hθ hβ1 hβ2).2
    linarith
  have b6 : h * Emain θ β X' ≤ 6 * h + 12 * T := by
    have h1 := mul_le_mul_of_nonneg_left b5 hh0.le
    have e : h * (6 + 12 * (W * X / L)) = 6 * h + 12 * T := by rw [hT]; ring
    linarith
  have hE0 : 0 ≤ Emain θ β X := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hE'0 : 0 ≤ Emain θ β X' := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hEE : Emain θ β X ≤ Emain θ β X' := by linarith

  have q1 := (abs_le.1 (hQ X' hXX')).1
  have q2 := (abs_le.1 (hQ X le_rfl)).2
  have r1 : rhoErr Cr cr B X' * Emain θ β X' ≤ h / 100 * Emain θ β X' :=
    mul_le_mul_of_nonneg_right
      (le_trans (gl2a4_rho_mono hCr hcr (by linarith) hX1.le hXX') hρ) hE'0
  have r2 : rhoErr Cr cr B X * Emain θ β X ≤ h / 100 * Emain θ β X' :=
    mul_le_mul hρ hEE hE0 (by positivity)
  have s1 : Real.sqrt X' ≤ 3 / 2 * u ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (3 / 2 * u ^ 6) ^ 2 = 9 / 4 * X := by rw [← hu12]; ring
    rw [this]; linarith
  have s2 : G * (π₂ X' : ℝ) ≤ 3 * B * u ^ 6 := by
    have h1 : (π₂ X' : ℝ) ≤ 3 * u ^ 6 := by linarith [hπ₂ X' (by linarith)]
    calc G * (π₂ X' : ℝ) ≤ B * (3 * u ^ 6) := mul_le_mul hGB h1 (Nat.cast_nonneg _) hB0.le
      _ = 3 * B * u ^ 6 := by ring
  have s3 : 0 ≤ G * (π₂ X : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hlBu : 3 * Real.log B ≤ u := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hB0 _) hX
    rw [Real.log_rpow hB0] at h1
    linarith
  have s4 : G * η' X' ≤ B * u :=
    mul_le_mul hGB (le_trans (hη X').2 hlBu) (hη X').1 hB0.le
  have s5 : 0 ≤ G * η' X := mul_nonneg (by linarith) (hη X).1

  have hB7' : B ^ 7 ≤ h * u ^ 4 := by
    rw [← hcb, ← Real.rpow_ofNat]; exact hB7
  have f1 : B ^ 3 ≤ h * u ^ 4 :=
    le_trans (pow_le_pow_right₀ (by linarith) (by norm_num)) hB7'
  have f2 : 800 * B ^ 3 ≤ h * u ^ 5 := by
    have h1 : B ^ 3 * 800 ≤ h * u ^ 4 * u := mul_le_mul f1 (by linarith) (by norm_num) (by positivity)
    have e : h * u ^ 4 * u = h * u ^ 5 := by ring
    linarith
  have f3 : 8 * B ^ 3 * u ^ 6 * L ≤ 12 / 100 * h * u ^ 12 := by
    calc 8 * B ^ 3 * u ^ 6 * L ≤ 8 * B ^ 3 * u ^ 6 * (12 * u) :=
          mul_le_mul_of_nonneg_left hlogu (by positivity)
      _ = 12 / 100 * (800 * B ^ 3) * u ^ 7 := by ring
      _ ≤ 12 / 100 * (h * u ^ 5) * u ^ 7 := by gcongr
      _ = 12 / 100 * h * u ^ 12 := by ring
  have f5 : 1 / (2 * B ^ 2) * (h * X / L) ≤ T := by
    have e : T = W * (h * X / L) := by rw [hT]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hW1 (by positivity)
  have f4 : 4 * B * u ^ 6 ≤ 12 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) := by
    have e : 12 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) = 12 / 100 * h * u ^ 12 / (2 * B ^ 2 * L) := by
      rw [← hu12]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 4 * B * u ^ 6 * (2 * B ^ 2 * L) = 8 * B ^ 3 * u ^ 6 * L := by ring
    rw [e2]; exact f3
  have f6 : 12 / 100 * h + B * u ≤ B * u ^ 6 := by
    have h5 : u ^ 1 ≤ u ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [pow_one] at h5
    have h6 : u * 2 ≤ u * u ^ 5 := mul_le_mul_of_nonneg_left (by linarith) hu0.le
    have e6 : u * u ^ 5 = u ^ 6 := by ring
    rw [e6] at h6
    have h7 : B * (u * 2) ≤ B * u ^ 6 := mul_le_mul_of_nonneg_left h6 hB0.le
    have h8 : (1 : ℝ) * 1 ≤ B * u := mul_le_mul (by linarith) (by linarith) (by norm_num) hB0.le
    linarith

  set Δ := (π₁ X' : ℝ) - π₁ X with hΔ
  have m1 : 14 / 100 * T ≤ G * Δ := by
    have e : G * Δ = G * ((π₁ X' : ℝ) + π₂ X' + η' X') - G * ((π₁ X : ℝ) + π₂ X + η' X) - G * (π₂ X' : ℝ)
        + G * (π₂ X : ℝ) - G * η' X' + G * η' X := by rw [hΔ]; ring
    rw [e]
    linarith only [q1, q2, r1, r2, s2, s3, s4, s5, a1, a2, b6, f4, f5, f6]
  have hΔ0 : 0 ≤ Δ := by
    by_contra hneg0
    have hneg := not_le.1 hneg0
    have : G * Δ < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  have m2 : G * Δ ≤ B * Δ := mul_le_mul_of_nonneg_right hGB hΔ0
  have hR0 : 0 < h * X / L := by positivity
  have m3 : 7 / 100 * (1 / B ^ 3) * (h * X / L) ≤ Δ := by
    have h1 : 14 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) ≤ B * Δ := by linarith
    have e : 7 / 100 * (1 / B ^ 3) * (h * X / L) = 14 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) / B := by
      field_simp; ring
    rw [e, div_le_iff₀ hB0]
    linarith
  have a4 : B ^ (-6 : ℝ) ≤ 1 / B ^ 3 := by
    have h1 : B ^ (-6 : ℝ) ≤ B ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : B ^ (-3 : ℝ) = 1 / B ^ 3 := by
      rw [Real.rpow_neg hB0.le, Real.rpow_ofNat, one_div]
    linarith
  have m4 : 1 / 100 * h * B ^ (-6 : ℝ) * X / L ≤ 7 / 100 * (1 / B ^ 3) * (h * X / L) := by
    have e : 1 / 100 * h * B ^ (-6 : ℝ) * X / L = 1 / 100 * B ^ (-6 : ℝ) * (h * X / L) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hR0.le
    have : 0 < 1 / B ^ 3 := by positivity
    linarith
  linarith

theorem shortIntervalLowerBound : ShortIntervalLowerBound := by
  intro C₀ Cr cr cb hC₀ hCr hcr hcb
  obtain ⟨Cm, hC0m, hC60, hCcb⟩ : ∃ Cm : ℝ, C₀ ≤ Cm ∧ 60 ≤ Cm ∧ 2 / cb ≤ Cm :=
    ⟨max C₀ (max 60 (2 / cb)), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  refine ⟨Cm, 1 / 100, hC0m, by norm_num, ?_⟩
  intro B G β θ π₁ π₂ η' hB hG1 hGB hθ hβ hπ₂ hη hQ X hX
  have hθ' : θ = -1 ∨ θ = 0 ∨ θ = 1 := by simpa using hθ
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hK := mul_log_le_log_of_rpow_le hB hX
  have hX60 : B ^ (60 : ℝ) ≤ X := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC60) hX
  have hXC₀ : B ^ C₀ ≤ X := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC0m) hX
  have hcbX : 2 / cb * Real.log B ≤ Real.log X :=
    le_trans (mul_le_mul_of_nonneg_right hCcb hlogB.le) hK
  obtain ⟨β', hβ1, hβ2, hE, hd⟩ := exists_adjusted_exceptional_exponent hcb hB hβ hcbX
  have hlow := Emain_lower_bound hθ' hB hβ1 hβ2 hd hX60
  refine ⟨?_, ?_⟩
  · rw [hE X]
    exact hlow
  · intro h hh1 hρ hB7
    refine exceptional_zero_contribution_bound hCr hcr hθ' hB hG1 hGB hβ1 hβ2 hd hX60 hπ₂ hη ?_ hh1 hρ hB7
    intro Y hY
    rw [← hE Y]
    exact hQ Y (le_trans hXC₀ hY)

private lemma numerical_exponential_inequality {Cr cr l L : ℝ} (hCr : 0 < Cr) (h60 : 60 * l ≤ L)
    (h16 : 16 * cr ^ 2 ≤ L) (h48 : 4800 / Cr ≤ L) (hL : 0 < L) :
    3 * Real.exp l * l ≤
      Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L) := by
  rcases le_or_gt l 0 with hl0 | hl0
  · have h1 : 3 * Real.exp l * l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hl0
    have h2 : 0 ≤ Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L) :=
      mul_nonneg (mul_nonneg hCr.le (Real.exp_pos _).le) (div_nonneg (by positivity) hL.le)
    linarith
  · have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    have hcs : cr * Real.sqrt L ≤ L / 4 := by nlinarith [sq_nonneg (Real.sqrt L - 4 * cr)]
    have hE : Real.exp (2 * L / 3) ≤ Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hll : l ≤ L / 60 := by linarith
    have hA : 0 < Real.exp (L / 60) := Real.exp_pos _
    have hel : Real.exp l ≤ Real.exp (L / 60) := Real.exp_le_exp.mpr hll
    have hy : 13 * L / 60 ≤ Real.exp (13 * L / 60) := by linarith [Real.add_one_le_exp (13 * L / 60)]
    have e3 : Real.exp (39 * L / 60) = Real.exp (13 * L / 60) ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hcube : (13 * L / 60) ^ 3 ≤ Real.exp (39 * L / 60) := by
      rw [e3]
      first
      | exact pow_le_pow_left₀ (by linarith) hy 3
      | exact pow_le_pow_left (by linarith) hy 3
    have e23 : Real.exp (L / 60) * Real.exp (39 * L / 60) = Real.exp (2 * L / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hK : 4800 ≤ Cr * L := by
      have := (div_le_iff₀ hCr).mp h48
      linarith
    have key : 3 * Real.exp l * l * (100 * L)
        ≤ Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) := by
      have k1 : 3 * Real.exp l * l ≤ 3 * Real.exp (L / 60) * (L / 60) :=
        mul_le_mul (by linarith) hll hl0.le (by positivity)
      have k2 : 3 * Real.exp (L / 60) * (L / 60) * (100 * L)
          ≤ Cr * (Real.exp (L / 60) * (13 * L / 60) ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hA.le (sq_nonneg L)) (sub_nonneg.mpr hK),
          mul_nonneg hA.le (sq_nonneg L)]
      have k3 : Cr * (Real.exp (L / 60) * (13 * L / 60) ^ 3)
          ≤ Cr * (Real.exp (L / 60) * Real.exp (39 * L / 60)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hA.le) hCr.le
      rw [e23] at k3
      have k4 : Cr * Real.exp (2 * L / 3)
          ≤ Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) :=
        mul_le_mul_of_nonneg_left hE hCr.le
      nlinarith [mul_le_mul_of_nonneg_right k1 (by linarith : (0 : ℝ) ≤ 100 * L)]
    have e : Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L)
        = Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) / (100 * L) := by
      first
      | ring
      | (field_simp; ring)
      | field_simp
    rw [e, le_div_iff₀ (by linarith)]
    exact key

theorem prime_divisor_count_absorption : PrimeDivisorCountAbsorption := by
  intro C₀ Cr cr cb hC₀ hCr hcr hcb
  obtain ⟨Cm, hC0m, hC60, hCcb, hC16, hC48⟩ : ∃ Cm : ℝ, C₀ ≤ Cm ∧ 60 ≤ Cm ∧ 2 / cb ≤ Cm ∧
      16 * cr ^ 2 ≤ Cm ∧ 4800 / Cr ≤ Cm :=
    ⟨max C₀ (max 60 (max (2 / cb) (max (16 * cr ^ 2) (4800 / Cr)))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))),
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))⟩
  refine ⟨Cm, hC0m, ?_⟩
  intro B G β θ P η' hB hG1 hGB hθ hβ hη hQ Y hY
  have hθ' : θ = -1 ∨ θ = 0 ∨ θ = 1 := by simpa using hθ
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogB : 0 < Real.log B := by linarith
  have hK := mul_log_le_log_of_rpow_le hB hY
  have hL60 : 60 * Real.log B ≤ Real.log Y := le_trans (mul_le_mul_of_nonneg_right hC60 hlogB.le) hK
  have hLC : Cm ≤ Real.log Y := le_trans (le_mul_of_one_le_right (by linarith) hlogB1) hK
  have hL16 : 16 * cr ^ 2 ≤ Real.log Y := le_trans hC16 hLC
  have hL48 : 4800 / Cr ≤ Real.log Y := le_trans hC48 hLC
  have hLpos : 0 < Real.log Y := by linarith
  have hcbX : 2 / cb * Real.log B ≤ Real.log Y :=
    le_trans (mul_le_mul_of_nonneg_right hCcb hlogB.le) hK
  have hY60 : B ^ (60 : ℝ) ≤ Y := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC60) hY
  have hYC₀ : B ^ C₀ ≤ Y := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC0m) hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hB0 _) hY
  obtain ⟨β', hβ1, hβ2, hE, hd⟩ := exists_adjusted_exceptional_exponent hcb hB hβ hcbX
  have hlow := Emain_lower_bound hθ' hB hβ1 hβ2 hd hY60
  rw [← hE Y] at hlow
  have hnum := numerical_exponential_inequality hCr hL60 hL16 hL48 hLpos
  rw [Real.exp_log hB0, Real.exp_log hY0] at hnum
  have e5 : Real.exp (-5 * Real.log B) = B ^ (-5 : ℝ) := by
    rw [Real.rpow_def_of_pos hB0]
    congr 1
    ring
  rw [e5] at hnum
  have hρ : Cr * Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ rhoErr Cr cr B Y := by
    unfold rhoErr
    linarith [mul_pos hCr (Real.exp_pos (-cr * Real.log Y / Real.log B))]
  have hm0 : 0 ≤ 1 / 100 * B ^ (-5 : ℝ) * Y / Real.log Y :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos hB0 _).le) hY0.le) hLpos.le
  have hρE : Cr * Real.exp (-cr * Real.sqrt (Real.log Y)) * (1 / 100 * B ^ (-5 : ℝ) * Y / Real.log Y)
      ≤ rhoErr Cr cr B Y * Emain θ β Y :=
    mul_le_mul hρ hlow hm0 (le_of_lt (gl2a4_rho_pos hCr))
  have hGη : G * η' Y ≤ B * (3 * Real.log B) := mul_le_mul hGB (hη Y).2 (hη Y).1 hB0.le
  have hGη0 : 0 ≤ G * η' Y := mul_nonneg (by linarith) (hη Y).1
  have h2 : rhoErr (2 * Cr) cr B Y = 2 * rhoErr Cr cr B Y := by
    unfold rhoErr
    ring
  have hQY := abs_le.mp (hQ Y hYC₀)
  rw [h2, abs_le]
  constructor <;> linarith [hQY.1, hQY.2]

theorem shortIntervalImpliesProgressions_statement : ShortIntervalImpliesProgressions := by
  intro hL C₀ Cr cr cb hC₀ hCr hcr hcb hQ
  obtain ⟨C₀', c, hC₀', hc, H⟩ := hL C₀ Cr cr cb hC₀ hCr hcr hcb
  refine ⟨C₀', c, lt_of_lt_of_le hC₀ hC₀', hc, ?_⟩
  intro m a hm ha Y h hY hh1 hρ h7
  obtain ⟨θ, β, η', hθ, hβ, hη, happrox⟩ := hQ m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : (4 : ℝ) ≤ 4 * m := by linarith
  have htot0 : 0 < m.totient := by
    first
    | exact Nat.totient_pos.mpr (by omega)
    | exact Nat.totient_pos (by omega)
  have htot1 : (1 : ℝ) ≤ (m.totient : ℝ) := by exact_mod_cast htot0
  have htotB : (m.totient : ℝ) ≤ 4 * m := by
    have h1 : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    linarith
  have key := (H (4 * m) (m.totient : ℝ) β θ
    (fun Z => ((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card) (fun _ => 0) η'
    hB htot1 htotB hθ hβ
    (fun Z _ => by
      show ((0 : ℕ) : ℝ) ≤ 2 * Real.sqrt Z
      rw [Nat.cast_zero]
      positivity)
    hη
    (fun Z hZ => by
      have hz := happrox Z hZ
      show |(m.totient : ℝ) * ((((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        + ((0 : ℕ) : ℝ) + η' Z) - Emain θ β Z| ≤ rhoErr Cr cr (4 * m) Z * Emain θ β Z
      rw [Nat.cast_zero, add_zero]
      exact hz)
    Y hY).2 h hh1 hρ h7
  have hY1 : (1 : ℝ) ≤ Y := by
    have h41 : (1 : ℝ) ≤ 4 * m := by linarith
    have := Real.one_le_rpow h41 (le_trans hC₀.le hC₀')
    linarith
  have hYpos : 0 < Y := by linarith
  have hY13 : 0 ≤ Y ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hYpos.le _
  have h47 : 0 < (4 * (m : ℝ)) ^ (7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpos : 0 < h := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hfl1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
  have hfl2 : ⌊Y⌋₊ ≤ ⌊Y * (1 + h)⌋₊ := Nat.floor_mono (by nlinarith)
  have hunion : Icc 1 ⌊Y * (1 + h)⌋₊ = Icc 1 ⌊Y⌋₊ ∪ Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a))
      ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter, Finset.mem_Icc] at hx1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx2
    omega
  have hcard : ((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
      = ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
        + ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card := by
    rw [hunion, Finset.filter_union]
    first
    | exact Finset.card_union_of_disjoint hdisj
    | exact Finset.card_disjoint_union hdisj
    | exact Finset.card_union_eq_card_add_card.mpr hdisj
  have key2 : c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        - (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ) := key
  rw [hcard, Nat.cast_add] at key2
  linarith

end ShortIntervalLowerBound

theorem parallelogram_maximum : ParallelogramMax := by
  intro T inst1 inst2 M₀ m hpar h0
  have hm : ∀ Q, Q ≠ 0 → m Q = 0 := by
    intro Q hQ
    have hsum : ∑ P : T, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P) = ∑ _P : T, 2 * m Q :=
      Finset.sum_congr rfl (fun P _ => hpar P Q hQ)
    have h1 : ∑ P : T, M₀ (P + Q) = ∑ P : T, M₀ P := Equiv.sum_comp (Equiv.addRight Q) M₀
    have h2 : ∑ P : T, M₀ (P - Q) = ∑ P : T, M₀ P := Equiv.sum_comp (Equiv.subRight Q) M₀
    have e1 : ∑ P : T, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P)
        = ∑ P : T, M₀ (P + Q) + ∑ P : T, M₀ (P - Q) - 2 * ∑ P : T, M₀ P := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∑ _P : T, 2 * m Q = (Fintype.card T : ℝ) * (2 * m Q) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
    have h3 : (Fintype.card T : ℝ) * (2 * m Q) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (ne_of_gt hc)
    · linarith
  refine ⟨hm, ?_⟩
  haveI : Nonempty T := ⟨0⟩
  obtain ⟨P, hP⟩ := Finite.exists_max M₀
  have hconst : ∀ R, M₀ R = M₀ P := by
    intro R
    by_cases hQ : R - P = 0
    · rw [sub_eq_zero.mp hQ]
    · have h1 := hpar P (R - P) hQ
      rw [hm _ hQ] at h1
      have e : P + (R - P) = R := by abel
      rw [e] at h1
      exact le_antisymm (hP R) (by linarith [hP (P - (R - P))])
  intro R
  have h00 := hconst 0
  rw [h0] at h00
  rw [hconst R]
  linarith

theorem prime_sums_short_interval_lower_bound_of_general : ShortIntervalLowerBound → Formalism.HermitianLattices.GL2PrimeSums.ShortIntervalLowerBound := by
  intro hL C₀ Cr cr cb h1 h2 h3 h4
  obtain ⟨C₀', c, hC, hc, H⟩ := hL C₀ Cr cr cb h1 h2 h3 h4
  refine ⟨C₀', c, hC, hc, ?_⟩
  intro B G β θ π₁ π₂ hB hG1 hGB hθ hβ hπ₂ hQ X hX
  exact H B G β θ π₁ π₂ (fun _ => 0) hB hG1 hGB hθ hβ hπ₂
    (fun _ => ⟨le_refl _, by
      show (0 : ℝ) ≤ 3 * Real.log B
      have := Real.log_nonneg (show (1 : ℝ) ≤ B by linarith)
      linarith⟩)
    (fun Y hY => by
      show |G * ((π₁ Y : ℝ) + π₂ Y + 0) - _| ≤ _
      rw [add_zero]
      exact hQ Y hY) X hX

theorem characters_cancel : CharactersCancelScalar := by
  intro A H inst1 inst2 χ m M M' g ϖ hg
  have hz : ∀ n : ℤ, (χ ^ n) ϖ = χ ϖ ^ n := by
    intro n
    first
    | rfl
    | simp
    | exact MonoidHom.zpow_apply χ n ϖ
  have key : (m * χ ^ (-M')) ϖ * (m⁻¹ * χ ^ M) ϖ = χ ϖ ^ (-g) := by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hz,
      mul_mul_mul_comm, mul_inv_cancel, one_mul, ← zpow_add, ← hg]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [key, zpow_neg, inv_inv]
  · rw [key, mul_inv_cancel]

theorem triangular_sum_exponent_bound : TriangularSumExponentBound := by
  intro m nT t f N sumW e1 he
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 : (m : ℝ) * e1 ≤ (m : ℝ) * (2 * sumW + f * N) := mul_le_mul_of_nonneg_left he hm
  have h3 : (m : ℝ) * (2 * sumW + f * N + nT * (t + 1) * ((m : ℝ) + 1) / 4)
      = (m : ℝ) * (2 * sumW + f * N) + nT * ((t + 1) / 2) * ((m : ℝ) * (m + 1) / 2) := by ring
  linarith [h2, h3]

theorem dimension_mass_joint_bound : DimensionMassJointBound := by
  intro f Dstar massr Isig dsig dimV hm hI hdim h3 hD
  have hprod : ∏ ρ ∈ range f, ((2 / 3 : ℝ) * dimV ρ) ≤ ∏ ρ ∈ range f, dsig ρ := by
    apply Finset.prod_le_prod
    · intro ρ hρ
      exact mul_nonneg (by norm_num) (hdim ρ (Finset.mem_range.mp hρ))
    · intro ρ hρ
      have := h3 ρ (Finset.mem_range.mp hρ)
      linarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod
  rw [hD]
  have hmI : 0 < massr * Isig := mul_pos hm hI
  calc (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ
      = massr * Isig * ((2 / 3 : ℝ) ^ f * ∏ ρ ∈ range f, dimV ρ) := by ring
    _ ≤ massr * Isig * ∏ ρ ∈ range f, dsig ρ := mul_le_mul_of_nonneg_left hprod hmI.le

theorem exponent_bounds : TableauExponentRange := by
  intro μ T j last first s nu1 hfirst hnu hs hnu1
  have hcard : (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ μ.rowLen 0 := by
    calc (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ (range (μ.rowLen 0)).card := by
          apply Finset.card_le_card_of_injOn (fun c => c.2)
          · intro c hc
            have hc' : c ∈ μ.cells ∧ T c.1 c.2 = j := by simpa using hc
            obtain ⟨i, k⟩ := c
            have h1 : (i, k) ∈ μ := hc'.1
            have h2 := μ.mem_iff_lt_rowLen.mp h1
            have h3 := μ.rowLen_anti 0 i (Nat.zero_le i)
            simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range]
            omega
          · intro a ha b hb hab
            have ha' : a ∈ μ.cells ∧ T a.1 a.2 = j := by simpa using ha
            have hb' : b ∈ μ.cells ∧ T b.1 b.2 = j := by simpa using hb
            obtain ⟨i, k⟩ := a
            obtain ⟨i', k'⟩ := b
            simp only at hab
            subst hab
            have hi : (i, k) ∈ μ := ha'.1
            have hi' : (i', k) ∈ μ := hb'.1
            have ea := ha'.2
            have eb := hb'.2
            simp only at ea eb
            rcases lt_trichotomy i i' with h | h | h
            · have := SemistandardYoungTableau.col_strict (T := T) h hi'
              exfalso
              omega
            · rw [h]
            · have := SemistandardYoungTableau.col_strict (T := T) h hi
              exfalso
              omega
      _ = μ.rowLen 0 := Finset.card_range _
  have hc : (((μ.cells.filter (fun c => T c.1 c.2 = j)).card : ℕ) : ℤ) ≤ (μ.rowLen 0 : ℤ) := by
    exact_mod_cast hcard
  refine ⟨by omega, by omega, max_le (by omega) hnu1⟩

theorem error_term_bound : ExponentBudgetLogBound := by
  intro ι inst1 W nT m t N b L logT C₀ hW hnT hm ht hN0 hNb htm hl0 hl
  have hc0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnT' : (nT : ℝ) ≤ Fintype.card ι := by exact_mod_cast hnT
  have hsumW0 : 0 ≤ ∑ τ, W τ := Finset.sum_nonneg (fun τ _ => (hW τ).1)
  have hsumW : ∑ τ, W τ ≤ (Fintype.card ι : ℝ) * (2 * b) := by
    calc ∑ τ, W τ ≤ ∑ _τ : ι, 2 * b := Finset.sum_le_sum (fun τ _ => (hW τ).2)
      _ = (Fintype.card ι : ℝ) * (2 * b) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA : (nT : ℝ) * ((t : ℝ) + 1) ≤ (Fintype.card ι : ℝ) * (2 * t) :=
    mul_le_mul hnT' (by linarith) (by positivity) hc0
  have hB : (nT : ℝ) * ((t : ℝ) + 1) * ((m : ℝ) + 1) ≤ (Fintype.card ι : ℝ) * (2 * t) * (2 * m) :=
    mul_le_mul hA (by linarith) (by positivity) (by positivity)
  have hC : (Fintype.card ι : ℝ) * ((t : ℝ) * m) ≤ (Fintype.card ι : ℝ) * b :=
    mul_le_mul_of_nonneg_left htm hc0
  have hD : (Fintype.card ι : ℝ) * N ≤ (Fintype.card ι : ℝ) * b :=
    mul_le_mul_of_nonneg_left hNb hc0
  have hE : 0 ≤ (Fintype.card ι : ℝ) * N := mul_nonneg hc0 hN0
  have hF : 0 ≤ (nT : ℝ) * ((t : ℝ) + 1) * ((m : ℝ) + 1) := by positivity
  have hBC : (Fintype.card ι : ℝ) * (2 * t) * (2 * m) = 4 * ((Fintype.card ι : ℝ) * ((t : ℝ) * m)) := by
    ring
  have hW2 : (Fintype.card ι : ℝ) * (2 * b) = 2 * ((Fintype.card ι : ℝ) * b) := by ring
  have hS0 : 0 ≤ 2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4 := by
    linarith
  have hS : 2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4
      ≤ 6 * ((Fintype.card ι : ℝ) * b) := by
    linarith
  have hCL : 0 ≤ C₀ * m * L := le_trans hl0 hl
  refine ⟨mul_nonneg hS0 hl0, ?_⟩
  calc (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * logT
      ≤ (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * (C₀ * m * L) :=
        mul_le_mul_of_nonneg_left hl hS0
    _ ≤ (6 * ((Fintype.card ι : ℝ) * b)) * (C₀ * m * L) := mul_le_mul_of_nonneg_right hS hCL
    _ = 6 * C₀ * Fintype.card ι * b * m * L := by ring

theorem discriminant_term_bound : DiscriminantTermBound := by
  intro k m L vE hm hmk hpi hL
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast le_trans hm hmk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hvE : 0 < vE := lt_of_lt_of_le Real.pi_pos hpi
  have hlog2v : Real.log (2 * vE) = Real.log 2 + Real.log vE := Real.log_mul (by norm_num) hvE.ne'
  have hlogpos : 0 ≤ Real.log (2 * vE) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have ha0 : 0 ≤ ((m : ℝ) - 1) / (2 * k) := div_nonneg (by linarith) (by linarith)
  have ha1 : ((m : ℝ) - 1) / (2 * k) ≤ 1 / 2 := by
    first
    | rw [div_le_iff₀ (by linarith)]
    | rw [div_le_iff (by linarith)]
    linarith
  constructor
  · have h1 : ((m : ℝ) - 1) / (2 * k) * Real.log (2 * vE) ≤ 1 / 2 * Real.log (2 * vE) :=
      mul_le_mul_of_nonneg_right ha1 hlogpos
    rw [neg_mul]
    linarith
  · rw [neg_mul]
    linarith [mul_nonneg ha0 hlogpos]

theorem hypotheses_of_third_theorem : RankThresholdInequalityEventually := by
  intro C L f m k hC hL hf hm hme hmk r p q
  have hr3 : 3 ≤ r := by
    show 3 ≤ k + m - 1
    omega
  have hqr : q ≤ r := by
    show m / 2 ≤ k + m - 1
    omega
  have hpr : p ≤ r := by
    show k + m / 2 - 1 ≤ k + m - 1
    omega
  have hR3 : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hR0 : (0 : ℝ) ≤ r := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := Real.add_one_le_exp (r : ℝ)
    have h2 : Real.exp (-(r : ℝ)) * Real.exp r = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := Real.exp_pos (-(r : ℝ))
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, mul_le_mul_of_nonneg_left hR3 h3.le]
  · obtain ⟨j, hj⟩ := hme
    show k + m / 2 - 1 + m / 2 = k + m - 1
    omega
  · show min (k + m / 2 - 1) (m / 2) = m / 2
    apply min_eq_right
    omega
  · have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hQ : (q : ℝ) ≤ r := by exact_mod_cast hqr
    have hpq : p * q ≤ r ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hpr hqr
    have hPQ : ((p * q : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hpq
    have hPQ0 : (0 : ℝ) ≤ ((p * q : ℕ) : ℝ) := Nat.cast_nonneg _
    have hR1 : (1 : ℝ) ≤ r := by linarith
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hR1
    have hlogr : Real.log r ≤ r := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)
      linarith
    have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hp3 : ((p * q : ℕ) : ℝ) ^ 3 ≤ ((r : ℝ) ^ 2) ^ 3 := by
      first
      | exact pow_le_pow_left₀ hPQ0 hPQ 3
      | exact pow_le_pow_left hPQ0 hPQ 3
    have a1 : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 ≤ r * ((r : ℝ) ^ 2) ^ 3 :=
      mul_le_mul hQ hp3 (by positivity) hR0
    have a2 : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r ≤ r * ((r : ℝ) ^ 2) ^ 3 * r * r := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right a1 hR0) hlogr hlog0
      positivity
    have a3 : (r : ℝ) ^ 9 ≤ (r : ℝ) ^ 19 := by
      first
      | exact pow_le_pow_right₀ hR1 (by norm_num)
      | exact pow_le_pow_right hR1 (by norm_num)
    have hf5 : (1 : ℝ) ≤ (f : ℝ) ^ 5 := by
      first
      | exact one_le_pow₀ hf1
      | exact one_le_pow_of_one_le' hf1 5
    have a4 : (1 : ℝ) ≤ (f : ℝ) ^ 5 * L := by nlinarith
    have a5 : (r : ℝ) ^ 19 ≤ (r : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) :=
      le_mul_of_one_le_right (by positivity) a4
    have e1 : r * ((r : ℝ) ^ 2) ^ 3 * r * r = (r : ℝ) ^ 9 := by ring
    have hX : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r ≤ (r : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) := by
      linarith
    have e2 : C * (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r / (1 / 3 : ℝ) ^ 2
        = 9 * C * ((q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r) := by ring
    rw [e2]
    have h9 := mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ 9 * C)
    linarith

private theorem sum_filter_neg_mul_val_eq_of_sign_split {E : Type} [Fintype E] [DecidableEq E] (S T : Finset E)
    (p : E → Prop) {dp : DecidablePred p} (i : ℤ) (val s' : E → ℤ) (hdisj : Disjoint S T)
    (hS : ∀ τ ∈ S, val τ = i) (hT : ∀ τ ∈ T, val τ = -i)
    (h0 : ∀ τ, τ ∉ S → τ ∉ T → val τ = 0) :
    ∑ τ ∈ univ.filter p, -(s' τ) * val τ =
      -i * (∑ τ ∈ S.filter p, s' τ - ∑ τ ∈ T.filter p, s' τ) := by
  have hval : ∀ τ, val τ = (if τ ∈ S then i else 0) + (if τ ∈ T then -i else 0) := by
    intro τ
    by_cases h1 : τ ∈ S
    · have h2 : τ ∉ T := Finset.disjoint_left.mp hdisj h1
      rw [if_pos h1, if_neg h2, hS τ h1, add_zero]
    · by_cases h2 : τ ∈ T
      · rw [if_neg h1, if_pos h2, hT τ h2, zero_add]
      · rw [if_neg h1, if_neg h2, h0 τ h1 h2, add_zero]
  have e1 : ∀ U : Finset E, ∑ τ ∈ univ.filter p, (if τ ∈ U then s' τ else 0)
      = ∑ τ ∈ U.filter p, s' τ := by
    intro U
    first
    | rw [Finset.sum_ite_mem]
    | rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext τ
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  calc ∑ τ ∈ univ.filter p, -(s' τ) * val τ
      = ∑ τ ∈ univ.filter p,
          (-i * (if τ ∈ S then s' τ else 0) - -i * (if τ ∈ T then s' τ else 0)) := by
        apply Finset.sum_congr rfl
        intro τ _
        rw [hval τ]
        split_ifs <;> ring
    _ = -i * (∑ τ ∈ S.filter p, s' τ - ∑ τ ∈ T.filter p, s' τ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e1, mul_sub]

theorem valuation_formula : BRValuation := by
  intro Emb inst1 φ c κ τ₀ hdisj i val s' hS hcS h0
  haveI := Classical.decEq Emb
  exact sum_filter_neg_mul_val_eq_of_sign_split _ _ _ i val s' hdisj hS hcS h0

open Formalism.HermitianLattices.GL2PrimeSums in
theorem character_sum_lipschitz : LipschitzWeightedSums := by
  have hinv : ∀ u v : ℝ, 0 < u → u ≤ v → ∀ c : ℝ, 0 ≤ c → c / v ≤ c / u := by
    intro u v hu huv c hc
    have h1 := one_div_le_one_div_of_le hu huv
    calc c / v = c * (1 / v) := by ring
      _ ≤ c * (1 / u) := mul_le_mul_of_nonneg_left h1 hc
      _ = c / u := by ring
  have hnr : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    first
    | exact Complex.norm_real r
    | simp
    | exact Complex.abs_ofReal r
  refine ⟨?_, ?_⟩
  · intro a S ha A w₀ w₁ w₂ hw₀ h01 h12 h2A
    have hw₁ : 0 < w₁ := lt_of_lt_of_le hw₀ h01
    have hw₂ : 0 < w₂ := lt_of_lt_of_le hw₁ h12
    have hA : 0 < A := lt_of_lt_of_le hw₂ h2A
    have hform : ∀ w : ℝ, 0 < w → (w : ℂ) * Gchi a S (A / w)
        = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / n - w : ℝ) : ℂ) - (A : ℂ) * S := by
      intro w hw
      have hwne : w ≠ 0 := hw.ne'
      have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hwne
      have h1 : (w : ℂ) * ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / w / n - 1 : ℝ) : ℂ)
          = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / n - w : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        have e : w * (A / w / n - 1) = A / n - w := by
          rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hwne]
        rw [← e]
        push_cast
        ring
      have h2 : (w : ℂ) * (((A / w : ℝ) : ℂ) * S) = (A : ℂ) * S := by
        rw [← mul_assoc]
        congr 1
        push_cast
        first
        | (field_simp; ring)
        | field_simp
      simp only [Gchi]
      rw [mul_sub, h1, h2]
    have hq : A / w₂ ≤ A / w₁ := hinv w₁ w₂ hw₁ h12 A hA.le
    have hN21 : ⌊A / w₂⌋₊ ≤ ⌊A / w₁⌋₊ := Nat.floor_mono hq
    have hsplit : Icc 1 ⌊A / w₁⌋₊ = Icc 1 ⌊A / w₂⌋₊ ∪ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 1 ⌊A / w₂⌋₊) (Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1
      rw [Finset.mem_Ioc] at hx2
      omega
    have hU : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ) := by
      rw [hsplit, Finset.sum_union hdisj]
    have hD : ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₂ : ℝ) : ℂ)
        - ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    have hX : ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
      rw [norm_mul, hnr, abs_of_nonpos (by linarith)]
      exact le_of_eq (by ring)
    have hY : ‖∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlow : w₁ ≤ A / n := by
        have h1 : (n : ℝ) ≤ A / w₁ :=
          le_trans (by exact_mod_cast hn.2) (Nat.floor_le (div_nonneg hA.le hw₁.le))
        rw [le_div_iff₀ hn0]
        rw [le_div_iff₀ hw₁] at h1
        linarith
      have hup : A / n < w₂ := by
        have h1 : A / w₂ < (n : ℝ) := by
          have h3 := Nat.lt_floor_add_one (A / w₂)
          have h2 : ((⌊A / w₂⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn.1
          linarith
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hw₂] at h1
        linarith
      rw [norm_mul, hnr, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have hsum : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, ‖a n‖ ≤ 2 * (A / w₁) := ha (A / w₁) (div_nonneg hA.le hw₁.le)
    rw [hsplit, Finset.sum_union hdisj] at hsum
    have hAw : A / w₁ ≤ A / w₀ := hinv w₀ w₁ hw₀ h01 A hA.le
    have hAw0 : 0 ≤ A / w₀ := div_nonneg hA.le hw₀.le
    have hS : (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁))
        + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁)
        = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖) * (w₂ - w₁) := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [hform w₂ hw₂, hform w₁ hw₁]
    calc ‖_‖ = ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)
          - ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖ := by
          congr 1
          linear_combination hD - hU
      _ ≤ ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)‖
          + ‖∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁))
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁) := add_le_add hX hY
      _ = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖) * (w₂ - w₁) := hS
      _ ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 3 * A / w₀ * (w₂ - w₁) := by
          have e : 3 * A / w₀ = 3 * (A / w₀) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · intro a ha0 ha A w₀ w₁ w₂ hw₀ h01 h12 h2A
    have hw₁ : 0 < w₁ := lt_of_lt_of_le hw₀ h01
    have hw₂ : 0 < w₂ := lt_of_lt_of_le hw₁ h12
    have hA : 0 < A := lt_of_lt_of_le hw₂ h2A
    have hform : ∀ w : ℝ, 0 < w → w * Gone a (A / w)
        = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / n - w)
          - A * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant) := by
      intro w hw
      have hwne : w ≠ 0 := hw.ne'
      have h1 : w * ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / w / n - 1)
          = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / n - w) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        have e : w * (A / w / n - 1) = A / n - w := by
          rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hwne]
        rw [← e]
        ring
      have hwA : w * (A / w) = A := by
        first
        | (field_simp; ring)
        | field_simp
      have h2 : w * (A / w * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant))
          = A * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant) := by
        rw [← mul_assoc, hwA]
      simp only [Gone]
      rw [mul_sub, h1, h2]
    have hq : A / w₂ ≤ A / w₁ := hinv w₁ w₂ hw₁ h12 A hA.le
    have hN21 : ⌊A / w₂⌋₊ ≤ ⌊A / w₁⌋₊ := Nat.floor_mono hq
    have hsplit : Icc 1 ⌊A / w₁⌋₊ = Icc 1 ⌊A / w₂⌋₊ ∪ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 1 ⌊A / w₂⌋₊) (Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1
      rw [Finset.mem_Ioc] at hx2
      omega
    have hbd : ∀ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, w₁ ≤ A / n ∧ A / n < w₂ := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlow : w₁ ≤ A / n := by
        have h1 : (n : ℝ) ≤ A / w₁ :=
          le_trans (by exact_mod_cast hn.2) (Nat.floor_le (div_nonneg hA.le hw₁.le))
        rw [le_div_iff₀ hn0]
        rw [le_div_iff₀ hw₁] at h1
        linarith
      have hup : A / n < w₂ := by
        have h1 : A / w₂ < (n : ℝ) := by
          have h3 := Nat.lt_floor_add_one (A / w₂)
          have h2 : ((⌊A / w₂⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn.1
          linarith
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hw₂] at h1
        linarith
      exact ⟨hlow, hup⟩
    have hU : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n * (A / n - w₁)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₁)
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁) := by
      rw [hsplit, Finset.sum_union hdisj]
    have hD : ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₂)
        - ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₁)
        = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₁ - w₂) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hY0 : 0 ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁) := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (ha0 n) (by linarith [(hbd n hn).1])
    have hY1 : ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁)
        ≤ (∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n) * (w₂ - w₁) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (by linarith [(hbd n hn).2]) (ha0 n)
    have hsum : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n ≤ 2 * (A / w₁) := ha (A / w₁) (div_nonneg hA.le hw₁.le)
    rw [hsplit, Finset.sum_union hdisj] at hsum
    have hS2 : 0 ≤ ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n := Finset.sum_nonneg (fun n _ => ha0 n)
    have hSI : 0 ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n := Finset.sum_nonneg (fun n _ => ha0 n)
    have hAw : A / w₁ ≤ A / w₀ := hinv w₀ w₁ hw₀ h01 A hA.le
    have hAw0 : 0 ≤ A / w₀ := div_nonneg hA.le hw₀.le
    have hLd : Real.log (A / w₁) - Real.log (A / w₂) = Real.log w₂ - Real.log w₁ := by
      rw [Real.log_div hA.ne' hw₁.ne', Real.log_div hA.ne' hw₂.ne']
      ring
    have hl0 : 0 ≤ Real.log w₂ - Real.log w₁ := by
      have := Real.log_le_log hw₁ h12
      linarith
    have hl1 : Real.log w₂ - Real.log w₁ ≤ (w₂ - w₁) / w₀ := by
      have h3 := Real.log_le_sub_one_of_pos (div_pos hw₂ hw₁)
      rw [Real.log_div hw₂.ne' hw₁.ne'] at h3
      have e : (w₂ - w₁) / w₁ = w₂ / w₁ - 1 := by rw [sub_div, div_self hw₁.ne']
      have h4 : (w₂ - w₁) / w₁ ≤ (w₂ - w₁) / w₀ := hinv w₀ w₁ hw₀ h01 (w₂ - w₁) (by linarith)
      linarith
    have hAl0 : 0 ≤ A * (Real.log w₂ - Real.log w₁) := mul_nonneg hA.le hl0
    have hAl1 : A * (Real.log w₂ - Real.log w₁) ≤ A * ((w₂ - w₁) / w₀) :=
      mul_le_mul_of_nonneg_left hl1 hA.le
    have hP1 : 0 ≤ (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₂ - w₁) := mul_nonneg hS2 (by linarith)
    have hP2 : ((∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n) * (w₂ - w₁)
        ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hR : 3 * A / w₀ * (w₂ - w₁) = (2 * (A / w₀)) * (w₂ - w₁) + A * ((w₂ - w₁) / w₀) := by ring
    have hnn : 0 ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_nonneg (by linarith) (by linarith)
    rw [hform w₂ hw₂, hform w₁ hw₁]
    calc |_| = |(∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₁ - w₂)
          - ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁)
          + A * (Real.log w₂ - Real.log w₁)| := by
          congr 1
          rw [← hLd]
          linear_combination hD - hU
      _ ≤ 3 * A / w₀ * (w₂ - w₁) := by
          rw [abs_le, hR]
          constructor <;> linarith

theorem rank_mul_pow_three_halves_le_fourth_power : RankMulPowThreeHalvesLeFourthPower := by
  intro f m k L hm hf hk hL
  have hqr : m / 2 ≤ k + m - 1 := by omega
  have hR1 : (1 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + m - 1)
  have hR0 : (0 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by linarith
  have hQ0 : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQR : ((m / 2 : ℕ) : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast hqr
  have h1 : ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ ((k + m - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hQ0 hQR (by norm_num)
  have h2 : ((k + m - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ ((k + m - 1 : ℕ) : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 := by
    have e : ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 = ((k + m - 1 : ℕ) : ℝ) ^ 3 := by ring
    rw [e]
    first
    | exact pow_le_pow_right₀ hR1 (by norm_num)
    | exact pow_le_pow_right hR1 (by norm_num)
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (1 : ℝ) ≤ (f : ℝ) ^ 5 := by
    first
    | exact one_le_pow₀ hf1
    | exact one_le_pow_of_one_le' hf1 5
  have h4 : (1 : ℝ) ≤ (f : ℝ) ^ 5 * L := by nlinarith
  have h5 : ((k + m - 1 : ℕ) : ℝ) ^ 19 ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) :=
    le_mul_of_one_le_right (by positivity) h4
  have h6 : ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hR0
  have h7 : ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) := h6.trans (h3.trans h5)
  have h8 := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 120)
  calc 120 * ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      = 120 * (((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by ring
    _ ≤ 120 * (((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L)) := h8
    _ = 120 * ((k + m - 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L := by ring

private theorem div_sub_val_div_mem_intRange_iff_cast_eq (q : ℕ) [Fact q.Prime] (a : ℤ) (r : ZMod q) :
    (a : ℚ) / q - (r.val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ) ↔ (a : ZMod q) = r := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  constructor
  · rintro ⟨k, hk⟩
    have h1 : (a : ℚ) = (r.val : ℚ) + k * q := by
      field_simp at hk
      linarith
    have h2 : a = (r.val : ℤ) + k * q := by exact_mod_cast h1
    rw [h2]
    push_cast
    simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
  · intro h
    have h1 : ((a - (r.val : ℤ) : ℤ) : ZMod q) = 0 := by
      push_cast
      rw [h]
      simp [ZMod.natCast_zmod_val]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
    refine ⟨k, ?_⟩
    have h2 : (a : ℚ) - (r.val : ℚ) = q * k := by exact_mod_cast hk
    field_simp
    linarith

private theorem natCard_subtype_eq_one_of_unique {α : Type} (P : α → Prop) (c : α) (hc : P c) (hu : ∀ a, P a → a = c) :
    Nat.card {a // P a} = 1 := by
  haveI : Unique {a // P a} := ⟨⟨⟨c, hc⟩⟩, fun a => Subtype.ext (hu a.1 a.2)⟩
  first
  | exact Nat.card_unique
  | simp

private theorem natCard_subtype_eq_zero_of_forall_not {α : Type} (P : α → Prop) (h : ∀ a, ¬ P a) :
    Nat.card {a // P a} = 0 := by
  haveI : IsEmpty {a // P a} := ⟨fun a => h a.1 a.2⟩
  first
  | exact Nat.card_of_isEmpty
  | simp

theorem kernel_description : IndicatorKernelSum := by
  intro q inst n n' fW x0 x hx0
  dsimp only
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  by_cases hI : ∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)
  swap
  · refine ⟨fun h => absurd h.1 hI, fun _ => ⟨?_, ?_⟩⟩
    · refine natCard_subtype_eq_zero_of_forall_not _ ?_
      intro a ha
      exact hI ha.2.1
    · refine natCard_subtype_eq_zero_of_forall_not _ ?_
      intro a ha
      exact hI ha.2.1
  have hI' := hI
  simp only [Set.mem_range] at hI'
  choose X hX using hI'
  have hmv : ∀ i, (x.mulVec (fun j => (x0 j : ℚ))) i = ((∑ j, X i j * x0 j : ℤ) : ℚ) := by
    intro i
    first
    | simp only [Matrix.mulVec, dotProduct]
    | simp only [Matrix.mulVec, Matrix.dotProduct]
    push_cast
    simp only [hX]
  have hme : ∀ i, (x.mulVec (fun j => (x0 j : ℚ) / q)) i = ((∑ j, X i j * x0 j : ℤ) : ℚ) / q := by
    intro i
    first
    | simp only [Matrix.mulVec, dotProduct]
    | simp only [Matrix.mulVec, Matrix.dotProduct]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [hX]
    ring
  have hw : ∀ j, (∑ i, (fW i : ℚ) * x i j) = ((∑ i, fW i * X i j : ℤ) : ℚ) := by
    intro j
    push_cast
    simp only [hX]
  have hzq : (∑ i, (fW i : ℚ) * (x.mulVec (fun j => (x0 j : ℚ))) i)
      = ((∑ i, fW i * ∑ j, X i j * x0 j : ℤ) : ℚ) := by
    first
    | (simp only [hmv]; push_cast; ring)
    | (simp only [hmv]; push_cast)
    | (simp only [hmv]; norm_cast)
  have hswap : (∑ j, (∑ i, fW i * X i j) * x0 j) = ∑ i, fW i * ∑ j, X i j * x0 j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨z, hzdef⟩ : ∃ z : ℤ, z = ∑ i, fW i * ∑ j, X i j * x0 j := ⟨_, rfl⟩
  rw [← hzdef] at hzq hswap
  have hrhs : ((∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧ ∃ z' : ℤ,
      (∑ i, (fW i : ℚ) * (x.mulVec (fun j => (x0 j : ℚ))) i) = z' ∧ (z' : ZMod q) = 1)
      ↔ (z : ZMod q) = 1 := by
    constructor
    · rintro ⟨_, z', h1, h2⟩
      rw [hzq] at h1
      have h3 : z = z' := by exact_mod_cast h1
      rw [h3]
      exact h2
    · intro h
      exact ⟨hI, z, hzq, h⟩
  have hUK : ∀ xW : Fin n' → ZMod q,
      ((∑ i, (fW i : ZMod q) * xW i) = 1 ∧ (∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
        (∀ i, (x.mulVec (fun j => (x0 j : ℚ) / q)) i - ((xW i).val : ℚ) / q
          ∈ Set.range (Int.cast : ℤ → ℚ)))
      ↔ (xW = fun i => ((∑ j, X i j * x0 j : ℤ) : ZMod q)) ∧ (z : ZMod q) = 1 := by
    intro xW
    have hc : (∀ i, (x.mulVec (fun j => (x0 j : ℚ) / q)) i - ((xW i).val : ℚ) / q
          ∈ Set.range (Int.cast : ℤ → ℚ))
        ↔ xW = fun i => ((∑ j, X i j * x0 j : ℤ) : ZMod q) := by
      simp only [hme, div_sub_val_div_mem_intRange_iff_cast_eq]
      constructor
      · intro h
        funext i
        exact (h i).symm
      · intro h i
        rw [h]
    have hsum : ∀ xW' : Fin n' → ZMod q, xW' = (fun i => ((∑ j, X i j * x0 j : ℤ) : ZMod q)) →
        (∑ i, (fW i : ZMod q) * xW' i) = (z : ZMod q) := by
      intro xW' h
      rw [h, hzdef]
      first
      | (push_cast; rfl)
      | push_cast
      | simp
    constructor
    · rintro ⟨h1, _, h3⟩
      have h4 := hc.mp h3
      exact ⟨h4, by rw [← hsum xW h4]; exact h1⟩
    · rintro ⟨h4, h5⟩
      exact ⟨by rw [hsum xW h4]; exact h5, hI, hc.mpr h4⟩
  have hKU : ∀ f : Fin n → ZMod q,
      ((∑ j, f j * (x0 j : ZMod q)) = 1 ∧ (∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
        (∀ j, ∃ z' : ℤ, (∑ i, (fW i : ℚ) * x i j) = z' ∧ (z' : ZMod q) = f j))
      ↔ (f = fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) ∧ (z : ZMod q) = 1 := by
    intro f
    have hc : (∀ j, ∃ z' : ℤ, (∑ i, (fW i : ℚ) * x i j) = z' ∧ (z' : ZMod q) = f j)
        ↔ f = fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q) := by
      constructor
      · intro h
        funext j
        obtain ⟨z', h1, h2⟩ := h j
        rw [hw j] at h1
        have h3 : (∑ i, fW i * X i j) = z' := by exact_mod_cast h1
        rw [← h2, ← h3]
      · intro h j
        exact ⟨_, hw j, by rw [h]⟩
    have hsum : ∀ f' : Fin n → ZMod q, f' = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) →
        (∑ j, f' j * (x0 j : ZMod q)) = (z : ZMod q) := by
      intro f' h
      rw [h, ← hswap]
      first
      | (push_cast; rfl)
      | push_cast
      | simp
    constructor
    · rintro ⟨h1, _, h3⟩
      have h4 := hc.mp h3
      exact ⟨h4, by rw [← hsum f h4]; exact h1⟩
    · rintro ⟨h4, h5⟩
      exact ⟨by rw [hsum f h4]; exact h5, hI, hc.mpr h4⟩
  refine ⟨fun hr => ⟨?_, ?_⟩, fun hr => ⟨?_, ?_⟩⟩
  · have hz1 := hrhs.mp hr
    refine natCard_subtype_eq_one_of_unique _ (fun i => ((∑ j, X i j * x0 j : ℤ) : ZMod q)) ?_ ?_
    · exact (hUK _).mpr ⟨rfl, hz1⟩
    · intro a ha
      exact ((hUK a).mp ha).1
  · have hz1 := hrhs.mp hr
    refine natCard_subtype_eq_one_of_unique _ (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) ?_ ?_
    · exact (hKU _).mpr ⟨rfl, hz1⟩
    · intro a ha
      exact ((hKU a).mp ha).1
  · refine natCard_subtype_eq_zero_of_forall_not _ ?_
    intro a ha
    exact hr (hrhs.mpr ((hUK a).mp ha).2)
  · refine natCard_subtype_eq_zero_of_forall_not _ ?_
    intro a ha
    exact hr (hrhs.mpr ((hKU a).mp ha).2)

theorem inv_norm_sq_conj_ratio_pow_identities : InvNormSqConjRatioPowIdentities := by
  intro z g hz
  have hc : (starRingEnd ℂ) z ≠ 0 := (map_ne_zero _).mpr hz
  have hn : ‖z / (starRingEnd ℂ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz)]
  have hA : z ^ g ≠ 0 := pow_ne_zero g hz
  have hC : (starRingEnd ℂ) z ^ g ≠ 0 := pow_ne_zero g hc
  refine ⟨?_, ?_, ?_⟩
  · first
    | rw [norm_mul, norm_inv, norm_pow, norm_pow, hn, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg z)]
    | simp [norm_mul, norm_inv, norm_pow, hn, Complex.normSq_nonneg, hz]
  · rw [← Complex.mul_conj, mul_pow, div_pow,
      show (starRingEnd ℂ) z ^ (2 * g) = ((starRingEnd ℂ) z ^ g) ^ 2 by ring]
    field_simp
    try ring
  · rw [← Complex.mul_conj, mul_pow, div_pow, show z ^ (2 * g) = (z ^ g) ^ 2 by ring]
    field_simp
    try ring

theorem moduli_minimum_bound : Ms_min := by
  intro K inst1 inst2 hTC x hx
  have hxK : (x : K) ≠ 0 := by
    first
    | simpa using hx
    | exact fun h => hx (by exact_mod_cast h)
  have hwpos : ∀ w : NumberField.InfinitePlace K, 0 < w (x : K) := fun w => w.pos_iff.mpr hxK
  have hmult : ∀ w : NumberField.InfinitePlace K, w.mult = 2 := by
    intro w
    have hc := hTC.isComplex w
    first
    | exact NumberField.InfinitePlace.mult_isComplex ⟨w, hc⟩
    | (simp only [NumberField.InfinitePlace.mult]
       rw [if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc)])
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (x : K)
  simp only [hmult] at hprod
  have hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) := by
    have h1 : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) := Algebra.coe_norm_int x
    have h2 : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    have h3 : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs h2
    rw [← h1]
    exact_mod_cast h3
  have hsum : ∑ w : NumberField.InfinitePlace K, Real.log (w (x : K) ^ 2)
      = Real.log (∏ w : NumberField.InfinitePlace K, w (x : K) ^ 2) := by
    rw [Real.log_prod]
    intro w _
    exact pow_ne_zero 2 (hwpos w).ne'
  have hlogprod : 0 ≤ Real.log (∏ w : NumberField.InfinitePlace K, w (x : K) ^ 2) := by
    rw [hprod]
    exact Real.log_nonneg hN
  have hpt : ∀ w : NumberField.InfinitePlace K, 1 + Real.log (w (x : K) ^ 2) ≤ w (x : K) ^ 2 := by
    intro w
    have := Real.log_le_sub_one_of_pos (pow_pos (hwpos w) 2)
    linarith
  calc (Fintype.card (NumberField.InfinitePlace K) : ℝ)
      = ∑ _w : NumberField.InfinitePlace K, (1 : ℝ) := by simp
    _ ≤ ∑ w : NumberField.InfinitePlace K, (1 + Real.log (w (x : K) ^ 2)) := by
        rw [Finset.sum_add_distrib, hsum]
        linarith
    _ ≤ ∑ w : NumberField.InfinitePlace K, w (x : K) ^ 2 := Finset.sum_le_sum (fun w _ => hpt w)

section T2

open NumberField
open Formalism.LogVandermondeBounds.StandardLattice

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

theorem log_l_value_field_bound : LogLFunctionEulerBound := by
  intro K _ _ _ hK M hM
  have hpos : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (euler_factor_log_bound K hK M (by omega) P.1 P.2).1
  have hpart := partial_sums_log_euler_factor_le K hK M hM
  have habs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) hpart
  have hsum : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := habs.of_abs
  have hprod : Real.exp (∑' P : {P : Ideal (𝓞 K) // P.IsMaximal},
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) = Formalism.HermitianLatticesTheory.lValEta K M :=
    Real.rexp_tsum_eq_tprod hpos hsum
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · rw [← hprod]; exact Real.exp_pos _
  · rw [← hprod, Real.log_exp]
    calc |∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun P :
            {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
            (by simpa [Real.norm_eq_abs] using habs)
      _ ≤ _ := habs.tsum_le_of_sum_le hpart

end T2

end Formalism.HermitianLattices.GlobalBoundRefinements
