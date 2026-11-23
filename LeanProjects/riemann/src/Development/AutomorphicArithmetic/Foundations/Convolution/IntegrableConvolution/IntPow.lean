import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AdjInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H)

private theorem int_cv (f e g : TI K n) (hg : ∀ x, g x = cv ν f e x) :
    π.integrated ν (UnitaryRep.ccToL1 ν g) =
      π.integrated ν (UnitaryRep.ccToL1 ν f) * π.integrated ν (UnitaryRep.ccToL1 ν e) := by
  obtain ⟨g', h1, -, h2⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _)
    continuous_id ν ν f e
  have hgg : g = g' := by
    ext x
    rw [hg, h1]
    rfl
  subst hgg
  rw [h2 H π]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
  rfl

private theorem int_pow (a : TI K n) (k : ℕ) :
    ∃ c : TI K n, (∀ g, c g = cvPow ν a k g) ∧
      π.integrated ν (UnitaryRep.ccToL1 ν c) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (k + 1) := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hT⟩ := ih
    obtain ⟨h1, h2, -⟩ := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup K n) ν a c a a.continuous a.hasCompactSupport
      c.continuous c.hasCompactSupport a.continuous a.hasCompactSupport
    have hfun : (c : archGroup K n → ℂ) = cvPow ν a k := funext hc
    refine ⟨⟨⟨cv ν a c, h1⟩, h2⟩, fun g => ?_, ?_⟩
    · change cv ν a c g = cv ν a (cvPow ν a k) g
      rw [hfun]
    · rw [int_cv ν π a c _ (fun _ => rfl), hT, pow_succ' _ (k + 1)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sqOp :
    UpperTheory.ConvolutionTheory.L1.SqOp := by
  intro K _ _ n ν _ b a aF m ha haF hb H _ _ _ π
  obtain ⟨-, hinv⟩ := (UpperTheory.ConvolutionTheory.Tf.unimod K n).1 ν
  let bs : TI K n := ⟨⟨fun x => conj (b x⁻¹),
      Complex.continuous_conj.comp (b.continuous.comp continuous_inv)⟩,
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z => conj z) (map_zero _)⟩
  obtain ⟨hadj, hnorm, -⟩ := UpperTheory.ConvolutionTheory.Tf.adjInt (archGroup K n) H π ν b bs (fun _ => rfl)
  have hT : π.integrated ν (UnitaryRep.ccToL1 ν a) =
      π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    exact int_cv ν π b bs a ha
  have hb1 : ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ ≤ 1 := hnorm.trans hb
  obtain ⟨c, hc, hcT⟩ := int_pow ν π a m
  have hcF : c = aF := by
    ext g
    rw [hc, haF]
  refine ⟨hT, ?_, ?_, hcF ▸ hcT⟩
  · rw [hT]
    exact mul_star_self_nonneg _
  · rw [hT]
    calc _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖star (π.integrated ν (UnitaryRep.ccToL1 ν b))‖ := norm_mul_le _ _
      _ = ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ := by rw [norm_star]
      _ ≤ 1 := mul_le_one₀ hb1 (norm_nonneg _) hb1
