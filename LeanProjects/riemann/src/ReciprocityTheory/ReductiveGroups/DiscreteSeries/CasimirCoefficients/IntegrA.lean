import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.HaarPolar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

lemma pOfB_inP (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) : inP ε (pOfB ε B) := by
  have hH : (pOfB ε B)ᴴ = pOfB ε B := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact pOfB_star ε B a b
  have hJ : pOfB ε B * Jm ε = -(Jm ε * pOfB ε B) := by
    ext a b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    cases ha : ε a <;> cases hb : ε b <;> simp [pOfB, ha, hb]
  refine ⟨?_, hJ⟩
  unfold inG
  rw [hH, hJ, neg_add_cancel]

lemma toM_toUJ {m : Matrix (Fin n) (Fin n) ℂ} (h : inUJ ε m) : toM (toUJ ε m) = m := by
  unfold toUJ
  rw [dif_pos h]

lemma norm_le_sqrt_hs_pOfB (B : Pt ε → Qt ε → ℂ) : ‖B‖ ≤ Real.sqrt (hs (pOfB ε B)) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
  have h1 : pOfB ε B a.1 b.1 = B a b := by simp [pOfB, a.2, b.2]
  rw [← h1]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (hs_entry_leVG _ _ _))

lemma exp_neg_le_rpow {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → Real.exp (-δ * t) ≤ C * (1 + t) ^ (-(N : ℝ)) := by
  set M : ℝ := (N : ℝ) + 1 with hMdef
  have hM : 0 < M := by positivity
  set m : ℝ := min 1 (δ / M) with hmdef
  have hm0 : 0 < m := lt_min one_pos (div_pos hδ hM)
  refine ⟨(m ^ N)⁻¹, by positivity, fun t ht => ?_⟩
  have hle : m * (1 + t) ≤ Real.exp (δ * t / M) := by
    have h1 : m ≤ 1 := min_le_left _ _
    have h2 : m ≤ δ / M := min_le_right _ _
    have h3 : m * t ≤ δ / M * t := mul_le_mul_of_nonneg_right h2 ht
    have h4 := Real.add_one_le_exp (δ * t / M)
    have h5 : δ * t / M = δ / M * t := by ring
    nlinarith
  have hpow : (m * (1 + t)) ^ N ≤ Real.exp (δ * t) := by
    calc (m * (1 + t)) ^ N ≤ Real.exp (δ * t / M) ^ N := pow_le_pow_left₀ (by positivity) hle N
      _ = Real.exp (N * (δ * t / M)) := (Real.exp_nat_mul _ N).symm
      _ ≤ Real.exp (δ * t) := by
          refine Real.exp_le_exp.2 ?_
          have hdt : 0 ≤ δ * t := by positivity
          rw [mul_div_assoc', div_le_iff₀ hM]
          nlinarith
  have hpos : 0 < (m * (1 + t)) ^ N := by positivity
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, neg_mul, Real.exp_neg, ← mul_inv, ← mul_pow]
  exact inv_anti₀ hpos hpow

lemma lintegral_exp_neg_norm_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-δ * ‖x‖)) ∂μ < ⊤ := by
  obtain ⟨C, hC, hb⟩ := exp_neg_le_rpow hδ (Module.finrank ℝ E + 1)
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-δ * ‖x‖)) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal C *
          ENNReal.ofReal ((1 + ‖x‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hb _ (norm_nonneg _))
    _ = ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (finite_integral_one_add_norm (μ := μ) (by push_cast; linarith))

theorem lintegral_lt_top_of_polar (hq : 1 ≤ q0 ε) (ν : Measure (UJ ε)) [ν.IsHaarMeasure]
    (F : UJ ε → ℝ≥0∞) (hF : Measurable F) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hb : ∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      F (toUJ ε (toMK k * NormedSpace.exp X)) ≤
        ENNReal.ofReal (M * Real.exp (-(δ + n * Real.sqrt (2 * q0 ε)) * Real.sqrt (hs X)))) :
    ∫⁻ g, F g ∂ν < ⊤ := by
  obtain ⟨C, hC, hpol⟩ := haar_polar_le ε hq ν
  have := compactSpace_KG ε
  have hK : muK ε Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  set c := Real.sqrt (2 * q0 ε) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hpt : ∀ B : Pt ε → Qt ε → ℂ,
      (∫⁻ k, F (toUJ ε (toMK k * NormedSpace.exp (pOfB ε B))) ∂(muK ε)) *
        ENNReal.ofReal (Real.exp (n * c * Real.sqrt (hs (pOfB ε B)))) ≤
      muK ε Set.univ * ENNReal.ofReal (M * Real.exp (-δ * ‖B‖)) := by
    intro B
    set r := Real.sqrt (hs (pOfB ε B)) with hrdef
    have hr : ‖B‖ ≤ r := norm_le_sqrt_hs_pOfB B
    have h0 : 0 ≤ M * Real.exp (-(δ + n * c) * r) := by positivity
    calc (∫⁻ k, F (toUJ ε (toMK k * NormedSpace.exp (pOfB ε B))) ∂(muK ε)) *
          ENNReal.ofReal (Real.exp (n * c * r))
        ≤ (∫⁻ _k, ENNReal.ofReal (M * Real.exp (-(δ + n * c) * r)) ∂(muK ε)) *
          ENNReal.ofReal (Real.exp (n * c * r)) := by
          gcongr with k
          exact hb k _ (pOfB_inP ε B)
      _ = muK ε Set.univ * ENNReal.ofReal (M * Real.exp (-(δ + n * c) * r) * Real.exp (n * c * r)) := by
          rw [lintegral_const, ENNReal.ofReal_mul h0, mul_comm (ENNReal.ofReal _) (muK ε _), mul_assoc]
      _ ≤ muK ε Set.univ * ENNReal.ofReal (M * Real.exp (-δ * ‖B‖)) := by
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
          rw [mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
          nlinarith
  have h1 : ∀ _ : Pt ε, (volume : Measure (Qt ε → ℂ)).IsAddHaarMeasure := fun _ => inferInstance
  have h2 : ∀ _ : Pt ε, SigmaFinite (volume : Measure (Qt ε → ℂ)) := fun _ => inferInstance
  have h3 : (volume : Measure (Pt ε → Qt ε → ℂ)).IsAddHaarMeasure := inferInstance
  calc ∫⁻ g, F g ∂ν
      ≤ C * ∫⁻ B : Pt ε → Qt ε → ℂ,
          (∫⁻ k, F (toUJ ε (toMK k * NormedSpace.exp (pOfB ε B))) ∂(muK ε)) *
            ENNReal.ofReal (Real.exp (n * c * Real.sqrt (hs (pOfB ε B)))) := hpol F hF
    _ ≤ C * ∫⁻ B : Pt ε → Qt ε → ℂ, muK ε Set.univ * ENNReal.ofReal (M * Real.exp (-δ * ‖B‖)) := by
        exact mul_le_mul_right (lintegral_mono fun B => hpt B) _
    _ = C * (muK ε Set.univ * (ENNReal.ofReal M *
          ∫⁻ B : Pt ε → Qt ε → ℂ, ENNReal.ofReal (Real.exp (-δ * ‖B‖)))) := by
        rw [lintegral_const_mul' _ _ hK]
        simp_rw [ENNReal.ofReal_mul hM]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top (ENNReal.mul_lt_top hK.lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_exp_neg_norm_lt_top _ hδ)))

theorem integrable_of_polar {E : Type*} [NormedAddCommGroup E] (hq : 1 ≤ q0 ε)
    (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (φ : UJ ε → E) (hφ : Continuous φ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hb : ∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖φ (toUJ ε (toMK k * NormedSpace.exp X))‖ ≤
        M * Real.exp (-(δ + n * Real.sqrt (2 * q0 ε)) * Real.sqrt (hs X))) :
    Integrable φ ν := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  exact lintegral_lt_top_of_polar hq ν (fun g => ‖φ g‖ₑ) hφ.enorm.measurable hM hδ fun k X hX => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb k X hX)

lemma min_bound {h c x : ℝ} (hh : 0 ≤ h) (hc : 0 < c) (hx : 0 ≤ x) :
    -(h / 8) * min x (Real.sqrt x / c) ≤ h / (32 * c ^ 2) + -(h / (8 * c)) * Real.sqrt x := by
  have hr : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hq : 0 < 1 / (4 * c ^ 2) := by positivity
  have hm : Real.sqrt x / c - 1 / (4 * c ^ 2) ≤ min x (Real.sqrt x / c) := by
    refine le_min ?_ (by linarith)
    have h0 : 0 ≤ (Real.sqrt x - 1 / (2 * c)) ^ 2 := sq_nonneg _
    have e : (Real.sqrt x - 1 / (2 * c)) ^ 2 = Real.sqrt x ^ 2 - Real.sqrt x / c + 1 / (4 * c ^ 2) := by
      field_simp
      ring
    nlinarith
  have e2 : h / (32 * c ^ 2) + -(h / (8 * c)) * Real.sqrt x =
      -(h / 8) * (Real.sqrt x / c - 1 / (4 * c ^ 2)) := by
    field_simp
    ring
  rw [e2]
  exact mul_le_mul_of_nonpos_left hm (by linarith)

end ReciprocityTheory.ChartRestriction.DS.S7
