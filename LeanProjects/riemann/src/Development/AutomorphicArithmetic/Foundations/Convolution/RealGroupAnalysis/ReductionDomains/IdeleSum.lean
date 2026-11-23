import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem ab_pow' {F : Type} [Field F] [NumberField F] (ρ : IdeleGroup F) (n : ℕ) :
    ab (ρ ^ n) = ab ρ ^ n := by
  induction n with
  | zero => simpa using M.ab_one (F := F)
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; exact M.ab_mul _ _

theorem UpperTheory.ConvolutionTheory.R2.M.ideleSum :
    ∀ (F : Type) [Field F] [NumberField F] (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C → 1 < ab ρ → ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) < ⊤ := by
  intro F _ _ C ρ hC hρ
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  obtain ⟨B, hB⟩ := hC.bddAbove_image hcont.continuousOn
  have hBC : ∀ c ∈ C, (ab c)⁻¹ ^ 2 ≤ B := fun c hc => hB ⟨c, hc, rfl⟩
  set q : ℝ := (ab ρ)⁻¹ ^ 2 with hq
  have hρ0 : 0 < ab ρ := by linarith
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have : (ab ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
    have h0 : 0 ≤ (ab ρ)⁻¹ := by positivity
    rw [hq]; nlinarith
  have hterm : ∀ n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) ≤
      ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
    intro n
    have hS : MeasurableSet ((ρ ^ n * ·) '' C) :=
      (hC.image (continuous_mul_left _)).measurableSet
    have hμ : ideleMeasure F ((ρ ^ n * ·) '' C) = ideleMeasure F C := by
      rw [Set.image_mul_left]; exact measure_preimage_mul _ _ _
    calc ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
        ≤ ∫⁻ _ in (ρ ^ n * ·) '' C, ENNReal.ofReal q ^ n * ENNReal.ofReal B ∂(ideleMeasure F) := by
          refine setLIntegral_mono' hS ?_
          rintro _ ⟨c, hc, rfl⟩
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (ab (ρ ^ n * c))⁻¹ ^ 2 = q ^ n * (ab c)⁻¹ ^ 2 := by
            rw [M.ab_mul, ab_pow', hq, mul_inv, mul_pow, inv_pow, inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
          rw [e]
          exact mul_le_mul_of_nonneg_left (hBC c hc) (by positivity)
      _ = ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
          rw [setLIntegral_const, hμ, mul_assoc]
  have hr : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hq1
  have hfin : ENNReal.ofReal B * ideleMeasure F C < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  calc ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
      ≤ ∑' n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) := lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := ENNReal.tsum_le_tsum hterm
    _ = (1 - ENNReal.ofReal q)⁻¹ * (ENNReal.ofReal B * ideleMeasure F C) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hr)) hfin
