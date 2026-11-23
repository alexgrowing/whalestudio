import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe

noncomputable section

namespace Formalism.L2.PairingIndexBounds.F

open Formalism.L2.G.Pend Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

def ltC (g : Formalism.MainNotions.GL3Theta.G1 p) (hLT : LTIso g) : ℂ_[p] := ((g.C.u : ℂ_[p]) * wToC p ((epOf hLT : (Formalism.L2.G.Pend.WW p)ˣ) : Formalism.L2.G.Pend.WW p))⁻¹

theorem ltC_ne_zero (g : Formalism.MainNotions.GL3Theta.G1 p) (hLT : LTIso g) : ltC g hLT ≠ 0 := by
  unfold ltC
  refine inv_ne_zero (mul_ne_zero (Units.ne_zero _) ?_)
  exact (Units.map (wToC p).toMonoidHom (epOf hLT)).ne_zero

end Formalism.L2.PairingIndexBounds.F
