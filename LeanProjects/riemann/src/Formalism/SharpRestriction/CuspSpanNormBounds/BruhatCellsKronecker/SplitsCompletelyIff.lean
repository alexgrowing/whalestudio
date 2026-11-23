import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.PrimeToDifferent

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have := dimS_eq D.R
  omega

theorem idxRows_eq (D : D7) (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    LocalBesselAndTopKernel.idxRows D = Formalism.FourierDecayAlt.Sz.rowIdx D.R.k D.R.rS (D.host.g 0 : ℝ) ^ D.R.f *
      Formalism.FourierDecayAlt.Sz.rowIdx D.R.k D.R.rS (D.host.g 1 : ℝ) ^ D.R.f := by
  unfold LocalBesselAndTopKernel.idxRows
  rw [finprod_typedPl D h0 h1
    (fun q => LocalBesselAndTopKernel.cardGL q D.R.r / (q ^ LocalBesselAndTopKernel.dimNS D * q ^ (D.R.k * (D.R.k - 1) / 2)))]
  unfold Formalism.FourierDecayAlt.Sz.rowIdx Formalism.FourierDecayAlt.Sz.glCard Formalism.FourierDecayAlt.Sz.dimN LocalBesselAndTopKernel.cardGL LocalBesselAndTopKernel.dimNS
  rw [rank_eq D]

end Formalism.MainNotions.BridgeLemma

end
