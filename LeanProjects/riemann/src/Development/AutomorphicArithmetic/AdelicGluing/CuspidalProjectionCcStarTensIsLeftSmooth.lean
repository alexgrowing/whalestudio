import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LeftSm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem conj_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) :
    (isExpLieAlgebra K n).IsSmoothFun fun g => conj (f g) := by
  letI := (isExpLieAlgebra K n).chartedSpace
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact hc.comp_contMDiff hf

theorem UpperTheory.cuspidalProjection_ccStar_tens_isLeftSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), SmoothT β →
          (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ u ∈ U, ∀ h, e (h * u) = e h) →
          IsLeftSmooth (CuspidalProjection.ccStar (tens β e)) := by
  intro K _ _ n hn β e hβ ⟨U, hUo, hU⟩
  let β' : TI K n := ⟨⟨fun a => conj (β a⁻¹), Complex.continuous_conj.comp (β.continuous.comp continuous_inv)⟩,
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
  let e' : TF K n := ⟨⟨fun a => conj (e a⁻¹), Complex.continuous_conj.comp (e.continuous.comp continuous_inv)⟩,
    (e.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
  have hL := UpperTheory.ConvolutionTheory.Tf.leftSm K n hn β e
  rw [hL.2 β' e' (fun _ => rfl) (fun _ => rfl)]
  refine (UpperTheory.ConvolutionTheory.Tf.leftSm K n hn β' e').1 ?_ ⟨U, hUo, fun u hu h => ?_⟩
  · have h1 := (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1
    exact conj_smooth ((isExpLieAlgebra K n).mem_smoothFuns.1 h1)
  · show conj (e (u * h)⁻¹) = conj (e h⁻¹)
    rw [mul_inv_rev, hU _ (U.inv_mem hu)]
