import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  first | exact @GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | exact GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | (intros; apply GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil <;> assumption)
