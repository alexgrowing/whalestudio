import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnOneLtRd
import Formalism.FlagUnipotentLattices.CoveringRadius2
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace Formalism.L2.S.S7.DensityConstant

open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)

def densityConstant (X : CData) (J : ℕ) (c : Composition J) : ℝ :=
  (X.I.rd / 2) ^ (-((X.I.f : ℝ) * (dimN c.blocksFun (X.I.n - 2 * J) : ℝ) / 2)) *
    (2 : ℝ) ^ (-((X.I.f : ℝ) * ((X.I.n : ℝ) * (J : ℝ) - (J : ℝ) ^ 2 + (J : ℝ) / 2))) *
    (Vsph (X.I.n - X.qq) * Vsph X.qq /
      (Vsph (X.I.n - X.qq - J) * Vsph (X.qq - J) * ∏ i, Vsph (c.blocksFun i))) ^ X.I.f *
    cn_res X ^ c.length *
    (∏ i, ∏ l ∈ Finset.Icc 2 (c.blocksFun i), ‖NumberField.dedekindZeta X.I.E (l : ℂ)‖) /
    ∏ M ∈ Finset.Ioc (X.I.n - 2 * J) X.I.n, Formalism.HermitianLatticesTheory.lValEta X.I.E M

end Formalism.L2.S.S7.DensityConstant

end
