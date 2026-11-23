import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem adelicWeightFour_eq_product {F : Type} [Field F] [NumberField F] (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y z : A F) :
    wt4 L N ![0, x, y, z] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N z) := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero, mul_assoc]

private theorem tsum_pi_fin_two_product {F : Type} (f : F → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, f (ξ 0) * f (ξ 1) = (∑' x, f x) * ∑' x, f x := by
  rw [← (finTwoArrowEquiv F).symm.tsum_eq, ENNReal.tsum_prod' ]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

private theorem real_bound {w b T c : ℝ} (hw : 0 ≤ w) (hb : 0 < b) (hT0 : 0 ≤ T) (hT : T ≤ c * (1 + b)) :
    b ^ 2 * (w * (T * T)) ≤ 2 * c ^ 2 * (w * b ^ 2 + w * b ^ 4) := by
  have h1 : T * T ≤ (c * (1 + b)) * (c * (1 + b)) := mul_le_mul hT hT hT0 (hT0.trans hT)
  have h2 : (c * (1 + b)) * (c * (1 + b)) ≤ 2 * c ^ 2 * (1 + b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]
  have h3 : b ^ 2 * w ≥ 0 := by positivity
  calc b ^ 2 * (w * (T * T)) = (b ^ 2 * w) * (T * T) := by ring
    _ ≤ (b ^ 2 * w) * (2 * c ^ 2 * (1 + b ^ 2)) := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.R2.G.zetaFin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ N : ℕ, ∀ L : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤ := by
  intro F _ _
  obtain ⟨A2, h2⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 2) (by norm_num)
  obtain ⟨A4, h4⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 4) (by norm_num)
  refine ⟨max (max A2 A4) (Module.finrank ℚ F + 1), fun L => ?_⟩
  set N := max (max A2 A4) (Module.finrank ℚ F + 1) with hN
  have hfr : Module.finrank ℚ F < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.EpConvB.theta_bound L hfr
  have I2 := h2 L N ((le_max_left _ _).trans (le_max_left _ _))
  have I4 := h4 L N ((le_max_right _ _).trans (le_max_left _ _))
  let w : IdeleGroup F → ℝ := fun b => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (b : A F)
  let G : IdeleGroup F → ℝ := fun b => 2 * c ^ 2 * (w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 2 + w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 4)
  have hG : Integrable G (ideleMeasure F) := by
    have e2 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (2 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have e4 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (4 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have J2 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) (ideleMeasure F) := e2 ▸ I2
    have J4 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) (ideleMeasure F) := e4 ▸ I4
    exact (J2.add J4).const_mul (2 * c ^ 2)
  have key : ∀ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ≤ ENNReal.ofReal (G a⁻¹) := by
    intro a
    obtain ⟨hs, hb⟩ := hc a
    have hf0 : ∀ x : F, 0 ≤ GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) :=
      fun x => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    set T : ℝ := ∑' x : F, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) with hTdef
    have hT0 : 0 ≤ T := tsum_nonneg hf0
    have hw0 : 0 ≤ w a⁻¹ := GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    have e : ∑' ξ : Fin 2 → F,
        ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
        ENNReal.ofReal (w a⁻¹ * (T * T)) := by
      have e1 : ∀ ξ : Fin 2 → F,
          ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
          ENNReal.ofReal (w a⁻¹) * ((fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 0) *
            (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 1)) := by
        intro ξ
        rw [adelicWeightFour_eq_product, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (hf0 _)]
      have t2 := tsum_pi_fin_two_product (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)))
      beta_reduce at t2
      simp_rw [e1]
      rw [ENNReal.tsum_mul_left, t2, ← ENNReal.ofReal_tsum_of_nonneg hf0 hs,
        ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hT0]
    have hbpos : 0 < (UpperTheory.ConvolutionTheory.R2.ab a)⁻¹ := inv_pos.mpr (M.ab_pos a)
    have hr := real_bound hw0 hbpos hT0 hb
    rw [e, M.wt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [G, M.ab_inv] using hr
  haveI : (ideleMeasure F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have h3 : ∫⁻ a : IdeleGroup F, ENNReal.ofReal (G a⁻¹) ∂(ideleMeasure F) = ∫⁻ b : IdeleGroup F, ENNReal.ofReal (G b) ∂(ideleMeasure F) :=
    lintegral_inv_eq_self (fun b => ENNReal.ofReal (G b))
  exact ne_top_of_le_ne_top (h3 ▸ hG.lintegral_lt_top.ne) (lintegral_mono key)
