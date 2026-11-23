import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
import GroundTheory.AutomorphicForms.MeasuresGL
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

theorem UpperTheory.heckeOperator_adjoint_inv_eq_heckeOperator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))),
          IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
          ∀ x : GL (Fin n) (w.adicCompletion K), ContinuousLinearMap.adjoint (Hop μ w J x⁻¹) = Hop μ w J x := by
  intro K _ _ n μ _ w J hJ hc x
  borelize (GL (Fin n) (w.adicCompletion K))
  let P : TopologicalSpace.PositiveCompacts (GL (Fin n) (w.adicCompletion K)) :=
    ⟨⟨J, hc⟩, by rw [hJ.interior_eq]; exact ⟨1, J.one_mem⟩⟩
  let m := Measure.haarMeasure P
  have hm : m J = 1 := Measure.haarMeasure_self (K₀ := P)
  have : m.IsInvInvariant := ⟨Measures.inv_eq_self_GL _ n m⟩
  have h1 := UpperTheory.ConvolutionTheory.C.hopOloc K n μ w m J x ⟨hc, hJ⟩ hm
  have h2 := UpperTheory.ConvolutionTheory.C.hopOloc K n μ w m J x⁻¹ ⟨hc, hJ⟩ hm
  have ad := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.2.1
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, h2, h1, ← integral_conj, ← integral_inv_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have e : rhoL μ w g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ w g) := by
    unfold rhoL
    rw [ad, map_inv]
  have e2 : g⁻¹ ∈ {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x⁻¹ * b} ↔
      g ∈ {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} := by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by rw [← inv_inv g, e]; group⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by rw [e]; group⟩
  classical
  beta_reduce
  rw [map_mul, e, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
  congr 1
  simp only [Set.indicator_apply, e2, Pi.one_apply]
  split_ifs <;> simp
