import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDense
import Mathlib
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_gaussian_convolutions : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  first | exact @GlobalTheory.narrowGauss_convolution_dense | exact GlobalTheory.narrowGauss_convolution_dense | (intros; apply GlobalTheory.narrowGauss_convolution_dense <;> assumption)
