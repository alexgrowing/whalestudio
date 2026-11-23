import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def movY (j : ℕ) (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank) :
    ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank :=
  Function.update (Function.update y ⟨j, by omega⟩
      (actO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) 1 k⁻¹ (y ⟨j, by omega⟩)))
    ⟨j + 1, by omega⟩ (actO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) k⁻¹ 1 (y ⟨j + 1, by omega⟩))

end GlobalTheory.RowKFix

end
