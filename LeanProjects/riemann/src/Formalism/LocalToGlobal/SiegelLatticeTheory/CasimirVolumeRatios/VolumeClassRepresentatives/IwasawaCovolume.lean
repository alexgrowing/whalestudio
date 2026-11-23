import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.L2.S.S7.IwasawaCovolume

open NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma

def volgU (N : ℕ) : ℝ := ∏ i ∈ Finset.range N, (2 * Real.pi) ^ (i + 1) / ((i.factorial : ℕ) : ℝ)

def covolR (X : CData) : ℝ :=
  volgU X.I.n ^ Fintype.card (InfinitePlace X.I.F) *
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm X.I.E X.I.n) (Formalism.MainNotions.StandardLattice.stdLat X.I.E X.I.n)

theorem volgU_pos (N : ℕ) : 0 < volgU N :=
  Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (by exact_mod_cast Nat.factorial_pos i)

end Formalism.L2.S.S7.IwasawaCovolume
