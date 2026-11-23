import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin
import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayArchConvFinAvg
import Development.AutomorphicArithmetic.TwistedTraces.ExistsContDiffArchMatrixExtensionOfSmooth
import Development.AutomorphicArithmetic.TwistedTraces.TensConvEqArchConv
import Development.AutomorphicArithmetic.TwistedTraces.FinAvgTensOfLeftInvariant

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_tens_conv_real_smoothT :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (κ γ : TI K n) (e : TF K n)
        (U : Subgroup (AdelicGLn.integralFiniteGL K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) →
        SmoothT κ → (∀ g, (κ g).im = 0) →
        (∀ u ∈ U, ∀ h, e ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e h) → CuspDecay μ (tens (conv ν κ γ) e) := by
  intro K _ _ n hn μ _ ν _ κ γ e U hU hκ him he
  have hκeq : ∀ g, (((κ g).re : ℝ) : ℂ) = κ g := fun g => by
    apply Complex.ext <;> simp [him g]
  have hsm : (isExpLieAlgebra K n).IsSmoothFun (fun A => (((κ A).re : ℝ) : ℂ)) := by
    have h : (fun A => (((κ A).re : ℝ) : ℂ)) = fun g => κ g := funext hκeq
    rw [h]
    exact hκ
  have hcs : HasCompactSupport (fun g => (κ g).re) :=
    κ.hasCompactSupport.comp_left (g := Complex.re) rfl
  obtain ⟨β, hβ, hβc, hβu, hβκ⟩ := UpperTheory.exists_contDiff_archMatrix_extension_of_smooth K n (fun g => (κ g).re) hsm hcs
  let φ : archGroup K n ≃ₜ* ArchUnits K n :=
    { Subgroup.topEquiv (G := ArchUnits K n) with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let m : archGroup K n ≃ᵐ ArchUnits K n := φ.toHomeomorph.toMeasurableEquiv
  have hmφ : (m : archGroup K n → ArchUnits K n) = φ := rfl
  haveI hH : (Measure.map m ν).IsHaarMeasure := by
    rw [hmφ]
    exact φ.isHaarMeasure_map ν
  have hint : ∀ f : archGroup K n → ℂ,
      ∫ A, f A ∂ν = ∫ A : ArchUnits K n, f ⟨A, Subgroup.mem_top A⟩ ∂(Measure.map m ν) := by
    intro f
    rw [integral_map_equiv m (fun A : ArchUnits K n => f ⟨A, Subgroup.mem_top A⟩)]
    rfl
  have hkey := UpperTheory.tens_conv_eq_archConv K n hn (Measure.map m ν) ν hint β hβ.continuous hβc hβu κ γ e
    (fun A => by rw [hβκ A]; exact (hκeq A).symm)
  rw [hkey, ← UpperTheory.finAvg_tens_of_leftInvariant K n hn U hU γ e he]
  exact UpperTheory.cuspDecay_archConv_finAvg K n μ (Measure.map m ν) β hβ hβc hβu U hU (tens γ e)
