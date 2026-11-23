import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtA
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_comp_diagonal_conj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ t, (M.J0 M₀ fun g => u (cD t g)) = ENNReal.ofReal (ab t)⁻¹ * M.J0 M₀ u := by
  intro F _ _ M₀ u hu hN t
  obtain ⟨β, hβ⟩ := M.wtEx F
  have h1 := M.wtOne F β hβ
  have hcm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  have hβ' : Measurable fun g => β (cD t⁻¹ g) := hβ.1.comp (hcm _)
  have hu' : Measurable fun g => u (cD t g) := hu.comp (hcm _)
  have hN' : ∀ b g, u (cD t (nU b * g)) = u (cD t g) := by
    intro b g
    rw [M.cD_mul, M.cD_nU, hN]
  have hc : ∀ g, ∫⁻ b, β (cD t⁻¹ (nU b * g)) ∂(adeleMeasure F) = ENNReal.ofReal (ab t)⁻¹ := by
    intro g
    have hf : Measurable fun b : A F => β (nU b * cD t⁻¹ g) :=
      hβ.1.comp ((M.continuous_nU.mul continuous_const).measurable)
    have hs : Measurable fun x : A F => (t : IdeleGroup F) • x := by
      have : Continuous fun x : A F => (t : IdeleGroup F) • x := by
        simp only [Units.smul_def, smul_eq_mul]
        exact continuous_const.mul continuous_id
      exact this.measurable
    have e := lintegral_map (μ := adeleMeasure F) hf hs
    rw [map_smul_adeleMeasure, lintegral_smul_measure, h1] at e
    have e2 : ∀ b : A F, β (cD t⁻¹ (nU b * g)) = β (nU ((t : IdeleGroup F) • b) * cD t⁻¹ g) := by
      intro b
      rw [M.cD_mul, M.cD_nU, inv_inv, Units.smul_def, smul_eq_mul, mul_comm b]
    simp_rw [e2]
    rw [← e, smul_eq_mul, mul_one]
    rfl
  have a1 := M.wtA F M₀ β (fun g => u (cD t g)) 1 hβ.1 h1 hu' hN'
  have a2 := M.wtA F M₀ (fun g => β (cD t⁻¹ g)) u _ hβ' hc hu hN
  have a3 := (M.cdMeas F M₀ t).lintegral_comp
    (f := fun h => u h * β (cD t⁻¹ h)) (hu.mul hβ')
  have e3 : ∀ g, β (cD t⁻¹ (cD t g)) = β g := by
    intro g
    rw [M.cD_cD, inv_mul_cancel, M.cD_one]
  simp only [e3] at a3
  rw [one_mul] at a1
  rw [← a1, a3, a2]
