import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC

def GamTrace : Prop := ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) →
  (gamM (Mt (diagonal z)⁻¹)ᵀ).trace = ∏ a, ∏ b, (1 + z a / z b)

end PositivityTheory.RgBcC
