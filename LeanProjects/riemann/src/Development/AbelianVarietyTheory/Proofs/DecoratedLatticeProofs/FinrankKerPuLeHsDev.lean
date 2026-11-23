import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubIdStatement
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem finrank_ker_Pu_le_hsDev (D : D7) (u : D.what₂.Word) :
    (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) ≤ hsDev D u := by
  unfold hsDev
  refine GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id (Kmat D.s u u) _ ?_
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : D.s.Pu u x = 0 := hx
  simp [Kmat, hx']

end GlobalTheory.Core.Rk
