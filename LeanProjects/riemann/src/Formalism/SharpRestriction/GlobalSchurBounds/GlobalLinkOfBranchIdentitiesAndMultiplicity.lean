import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Formalism.LocalToGlobal.GlobalTheory.TransposeBaseMatrixInfinity
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpMatch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnDiaMatch0FHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem tCV_of_ties (Fm : FamP eps) (tCl : tCVTies Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) :=
  tCV_of_tied Fm ColValS.colValOfTiedS_holds tCl

end Formalism.MainNotions

end
