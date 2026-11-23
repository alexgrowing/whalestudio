import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.ProdLeProdSubOneLe

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def K1 : ℝ := 4 ^ (D.R.rS + 1) * ((D.R.rS + 1).factorial : ℝ) ^ 2 * rho0 D ^ (2 * (D.R.rS + 1))

def sgnE : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.diagonal fun b => (-1 : D.host.E) ^ (D.R.rS - b.val)

def sgnO : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E) :=
  Matrix.diagonal fun b => (-1 : 𝓞 D.host.E) ^ (D.R.rS - b.val)

end Formalism.MainNotions.S.Pv.HH

end
