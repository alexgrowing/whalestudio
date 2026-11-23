import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.KerZeroPf

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

theorem main : PositivityTheory.RgBcC.KerZero := by
  intro n _ _ μ _ E κ hκ hr hf y hy
  refine GlobalTheory.CompanionTheory.KerUniq.main n μ E κ (GLs n) GlobalTheory.CompanionTheory.KerUniq.isOpen_GLs subset_rfl ?_ hκ hr ?_ y hy
  · intro y hy k₂
    have hk : (k₂.1).det ≠ 0 := by
      have h : k₂.1 * star k₂.1 = 1 := (Matrix.mem_unitaryGroup_iff).1 k₂.2
      intro h0
      have h1 := congrArg Matrix.det h
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    show (y * k₂.1).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hy hk
  · intro f hfE hc _
    have h := hf f hfE hc
    simpa [act] using h

end GlobalTheory.CompanionTheory.KerZeroPf
