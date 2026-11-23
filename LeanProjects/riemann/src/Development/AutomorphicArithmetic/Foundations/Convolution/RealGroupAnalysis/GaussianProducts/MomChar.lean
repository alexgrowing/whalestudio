import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momChar :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * ∑ i, |X ω i|) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ (n : ℕ) (t : ι → ℝ), ∫ ω, ((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω ∂ν = 0) →
    ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hint hmom t
  have hym : Measurable (fun ω => ∑ i, t i * X ω i) :=
    Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hX).const_mul (t i))
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hbound : ∀ ω, |∑ i, t i * X ω i| ≤ (∑ i, |t i|) * ∑ i, |X ω i| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => |X ω j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      (abs_nonneg _)
  have hdom : Integrable (fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖) ν := by
    refine (hint (∑ i, |t i|)).norm.mono'
      (((Real.measurable_exp.comp (continuous_abs.measurable.comp hym)).aestronglyMeasurable).mul hρ.norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, norm_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_norm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound ω)) (norm_nonneg (ρ ω))
  have hsum := hasSum_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) ω => (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω)
    (f := fun ω => Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
    (fun (n : ℕ) ω => |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have hz : (fun n : ℕ => ∫ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω ∂ν)
        = fun _ => 0 := by
      funext n
      have : ∀ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω
          = (Complex.I ^ n / (n.factorial : ℂ)) * (((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω) := by
        intro ω; rw [mul_pow]; ring
      simp_rw [this]
      rw [integral_const_mul, hmom n t, mul_zero]
    rw [hz] at hsum
    exact hsum.unique hasSum_zero |>.symm ▸ rfl
  · have hc : Measurable (fun ω => ((∑ i, t i * X ω i : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hym
    exact ((((hc.mul_const Complex.I).pow_const n).div_const _).aestronglyMeasurable).mul hρ.aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
  · exact Eventually.of_forall fun ω =>
      (Real.summable_pow_div_factorial _).mul_right _
  · have : (fun ω => ∑' n : ℕ, |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
        = fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖ := by
      funext ω
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [this]; exact hdom
  · refine Eventually.of_forall fun ω => ?_
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)).mul_right (ρ ω)
    rwa [← Complex.exp_eq_exp_ℂ] at this
