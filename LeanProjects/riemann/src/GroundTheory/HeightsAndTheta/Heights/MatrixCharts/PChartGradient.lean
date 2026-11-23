import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCChartGradient

theorem u_eq (D : PeriodChartData) :
    D.u = fun q => logDetGram (D.Y q.1) (D.f q) := rfl

theorem bound_arith (S A C₁ δ r e : ℝ) (k : ℕ) (hS : 0 ≤ S) (hA : 0 ≤ A) (hC₁ : 0 < C₁)
    (hδ : 0 < δ) (hr : 0 < r) (he : 1 ≤ e) :
    S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) ≤ S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr
  have h1 : S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) =
      S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) := by
    rw [inv_pow, ← mul_pow]
    field_simp
  rw [h1]
  have h2 : S * (1 + A * e) ≤ S * (1 + A) * e := by
    nlinarith [mul_le_mul_of_nonneg_left he hS]
  have h3 : 0 ≤ C₁ ^ k * r ^ k / δ := by positivity
  calc S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) ≤ S * (1 + A) * e * (C₁ ^ k * r ^ k / δ) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by ring

theorem pow_le_rpow_of_le {r C : ℝ} {k : ℕ} (hr : 1 ≤ r) (hk : (k : ℝ) ≤ C) :
    r ^ k ≤ r ^ C := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hr hk

end MCChartGradient

open MCChartGradient in

theorem ChartGradient.proof (h₁ : LogDetGramDeriv.Statement) (h₂ : ChartFrameDeriv.Statement)
    (h₃ : ChartImagDeriv.Statement) (h₄ : ChartBounds.Statement) : ChartGradient.Statement := by
  intro D
  obtain ⟨K₀, hK₀, hK⟩ := h₁ D.g D.rk
  obtain ⟨AF, hAF, hF⟩ := h₂ D
  obtain ⟨AY, hAY, hY⟩ := h₃ D
  obtain ⟨C₁, hC₁, hB⟩ := h₄ D
  obtain ⟨δ, M, hδ, -, hG⟩ := MCBounds.exists_gram_bounds D
  have hc : 0 ≤ D.c⁻¹ := inv_nonneg.mpr D.c_pos.le
  set S : ℝ := K₀ * (1 + AF) ^ (2 * D.rk) * (1 + D.c⁻¹) ^ (D.rk + 1) with hSdef
  have hS : 0 ≤ S := by positivity
  set K' : ℝ := S * (1 + AY) * C₁ ^ D.rk / δ with hK'def
  have hK'0 : 0 ≤ K' := by positivity
  have hC1 : (1 : ℝ) ≤ max K' (max (D.rk : ℝ) 1) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max K' (max (D.rk : ℝ) 1), lt_of_lt_of_le one_pos hC1, fun p hp hps => ?_⟩
  set C := max K' (max (D.rk : ℝ) 1) with hCdef
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 : 1 ≤ D.radius p.1 := MCBounds.one_le_radius D hz
  set r := D.radius p.1 with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have he : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  obtain ⟨hYc, -, hdet, -, -, -⟩ := hB p hp hps
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr0
  have hμpos : 0 < (C₁ * r)⁻¹ ^ D.rk * δ := mul_pos (pow_pos (inv_pos.mpr hCr) _) hδ
  have hμ : (C₁ * r)⁻¹ ^ D.rk * δ ≤
      ((D.f p)ᴴ * (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) * D.f p).det.re :=
    le_trans (mul_le_mul_of_nonneg_left (hG p hp).1 (pow_nonneg (inv_pos.mpr hCr).le _)) hdet
  obtain ⟨hd, hn⟩ := hK (E := (Fin D.n → ℂ) × (Fin D.m → ℂ)) D.f (fun q => D.Y q.1) p AF
    (AY * Real.exp (r / 2)) D.c ((C₁ * r)⁻¹ ^ D.rk * δ) D.c_pos hμpos hAF.le
    (mul_nonneg hAY.le (Real.exp_pos _).le) (hF p hp) (fun j l => hY p hp hps j l) hYc hμ
  rw [u_eq]
  refine ⟨hd, hn.trans ?_⟩
  have hb := bound_arith S AY C₁ δ r (Real.exp (r / 2)) D.rk hS hAY.le hC₁ hδ hr0 he
  refine hb.trans ?_
  have hpow : r ^ D.rk ≤ r ^ C :=
    pow_le_rpow_of_le hr1 ((le_max_left _ _).trans (le_max_right _ _))
  have hKC : K' ≤ C := le_max_left _ _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hKC hpow (pow_nonneg hr0.le _) (by linarith)) (Real.exp_pos _).le

end

end GroundTheory.Heights₂.Heights
