import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.InfZcCoeff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LactCenGen
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ExpGen
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DiracSep
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

private theorem UpperTheory.ConvolutionTheory.Dp.sInfIff_uC {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    (p q : UEnv E n) (ψ : cuspForms E n) :
    Cm.uC E n ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) (Cm.ofCusp E n ψ) =
      Cm.ofCusp E n (uActionCusp E n p ψ + Complex.I • uActionCusp E n q ψ) := by
  rw [map_add, map_add, map_smul, Cm.ofCusp_uAction, Cm.ofCusp_uAction, Cm.uC_tmul, Cm.uC_tmul, one_smul]
  rfl

theorem UpperTheory.ConvolutionTheory.Dp.sInfIff :
    UpperTheory.ConvolutionTheory.Dp.SInfIff := by
  intro E _ _ _ n μ _ π V h τ m
  rw [UpperTheory.ConvolutionTheory.Dp.infZc E n π τ m]
  have hcen := (UpperTheory.ConvolutionTheory.Dp.capZc E n τ).1
  have hform := (UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand).2.2.2
  have hcls := (UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ).1
  unfold SInf
  refine and_congr_right fun _ => ⟨fun H i φ hφ => ?_, fun H ν _ β hβ i v hv => ?_⟩
  · obtain ⟨p, hp, q, hq, hzc⟩ := Cm.exists_re_im_center (hcen i)
    rw [← Cm.map_carrier π] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    have hψ' : ψ ∈ formsIn μ V := h.carrier_eq ▸ hψ
    obtain ⟨hψc, hψV⟩ := hψ'
    have hz : clsL μ ((uActionCusp E n p ψ + Complex.I • uActionCusp E n q ψ) - m.esymm (i + 1) • ψ) = 0 := by
      refine UpperTheory.ConvolutionTheory.Dp.diracSep E n μ (Measure.haar : Measure (archGroup E n)) _ fun β hβ => ?_
      have h1 := H Measure.haar β hβ i _ hψV
      rw [hzc, UpperTheory.ConvolutionTheory.Dp.lactCen_of_gen E n (UpperTheory.ConvolutionTheory.Tf.expGen E n) μ Measure.haar β hβ p hp q hq ψ hψc] at h1
      rw [map_sub, map_smul, map_sub, map_smul, h1, sub_self]
    have hz0 := hcls _ (sub_mem (add_mem (uActionCusp_mem_centralCuspForms p hψc)
      (Submodule.smul_mem _ _ (uActionCusp_mem_centralCuspForms q hψc))) (Submodule.smul_mem _ _ hψc)) hz
    rw [hzc, sInfIff_uC, sub_eq_zero.1 hz0, map_smul]
  · obtain ⟨p, hp, q, hq, hzc⟩ := Cm.exists_re_im_center (hcen i)
    rw [hzc]
    have hclosed : IsClosed {v : LL μ | Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) v =
        m.esymm (i + 1) • Oinf μ ν β v} :=
      isClosed_eq (ContinuousLinearMap.continuous _) ((continuous_const_smul (m.esymm (i + 1))).comp (Oinf μ ν β).continuous)
    have hsub : (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆
        {v : LL μ | Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) v =
          m.esymm (i + 1) • Oinf μ ν β v} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      have hφ : Cm.ofCusp E n ψ ∈ π.V := Cm.mem_carrier.1 (h.carrier_eq.symm ▸ hψ)
      have e := H i _ hφ
      rw [hzc, sInfIff_uC] at e
      have e' := Cm.ofCusp_injective (e.trans (map_smul (Cm.ofCusp E n) _ ψ).symm)
      change Oinf μ ν _ (clsL μ ψ) = _
      rw [UpperTheory.ConvolutionTheory.Dp.lactCen_of_gen E n (UpperTheory.ConvolutionTheory.Tf.expGen E n) μ ν β hβ p hp q hq ψ hψ.1, e', map_smul, map_smul]
    have hv' : v ∈ ((formsIn μ V).map (clsL μ)).topologicalClosure := by rw [hform]; exact hv
    exact closure_minimal hsub hclosed hv'
