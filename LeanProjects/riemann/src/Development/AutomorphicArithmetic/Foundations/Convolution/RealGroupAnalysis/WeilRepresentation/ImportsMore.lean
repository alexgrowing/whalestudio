import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IwDens
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientRightInvariant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientCompDiagonalConj

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.inv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Inv F := by
  intro F _ _ _ M₀ u hu hN hi
  obtain ⟨ρ, -, hρ, hρ'⟩ := M.iwDens F M₀
  have hp : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hi' : Integrable (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) ρ := (hρ' _).1.2 hi
  refine ⟨fun g₀ => ?_, fun t => ?_⟩
  · have hg : Measurable fun g => u (g * g₀) := hu.comp (measurable_mul_const g₀)
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ρ) (hg.comp hp) (hu.comp hp) fun φ hφ =>
      (hρ (fun g => φ (u (g * g₀))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_right_invariant F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) g₀).trans
          (hρ (fun g => φ (u g)) (hφ.comp hu)).symm)
    exact ⟨(hρ' _).1.1 (h1.2 hi'), (hρ' _).2.symm.trans (h2.trans (hρ' _).2)⟩
  · have hg : Measurable fun g => u (cD t g) := hu.comp (M.continuous_cD t).measurable
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ENNReal.ofReal (ab t)⁻¹ • ρ) (hg.comp hp) (hu.comp hp) fun φ hφ => by
      rw [lintegral_smul_measure, smul_eq_mul]
      exact (hρ (fun g => φ (u (cD t g))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_comp_diagonal_conj F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) t).trans
          (congrArg _ (hρ (fun g => φ (u g)) (hφ.comp hu)).symm))
    refine ⟨(hρ' _).1.1 (h1.2 (hi'.smul_measure ENNReal.ofReal_ne_top)), (hρ' _).2.symm.trans (h2.trans ?_)⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (M.ab_pos t)).le, Complex.real_smul]
    exact congrArg _ (hρ' _).2
