import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInvGammaLeReflect
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.InvGammaStrip

theorem g0 : G0 := by
  intro a b
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gamma_le a b
  refine ⟨max (C * Real.exp Real.pi) Real.pi, fun z ha hb => ?_⟩
  have h1 := hC z ha hb
  set y := z.im
  have hy : |y| ≤ 1 + y ^ 2 := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg (y - 1/2), sq_nonneg (y + 1/2)]
  have hpi := Real.pi_pos
  have hM1 : C * Real.exp Real.pi ≤ max (C * Real.exp Real.pi) Real.pi := le_max_left _ _
  have hM2 : Real.pi ≤ max (C * Real.exp Real.pi) Real.pi := le_max_right _ _
  calc ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |y|) := h1
    _ ≤ C * Real.exp (Real.pi + Real.pi * y ^ 2) := by
        gcongr; nlinarith
    _ = C * Real.exp Real.pi * Real.exp (Real.pi * y ^ 2) := by rw [Real.exp_add]; ring
    _ ≤ max (C * Real.exp Real.pi) Real.pi * Real.exp (max (C * Real.exp Real.pi) Real.pi * y ^ 2) := by
        gcongr

end GlobalTheory.CompanionTheory.InvGammaStrip
