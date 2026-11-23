import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec

noncomputable section

open MeasureTheory Matrix PositivityTheory.Rg.Sw
open scoped Matrix ComplexConjugate

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

theorem gramX_tr_g (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX (fun _ : Fin m => true) x j i = ∑ a, star (x a j) * x a i := by
  simp [PositivityTheory.Rg.Sw.gramX, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.Qp,
    PositivityTheory.Rg.Sw.Qb]

end PositivityTheory.SiegelWeilFormula.KLI

end
