import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnTwistedArgsFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnTwistedArgsSecond
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.ArchFromLit

theorem archCmp_of_lit : LitLoc → LitAut → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL := by
  intro hLoc hAut hL
  exact
    { pht := GlobalTheory.PhtCompare.phtCmp
      lp := GlobalTheory.T.column_twisted_args_first hAut.art hLoc.chev hLoc.brauer hLoc.conv hLoc.exh hLoc.cos hLoc.bz hL
      cg := GlobalTheory.T.column_twisted_args_second hL hAut.fin hAut.js.1 hAut.cusp }

end GlobalTheory.ArchFromLit
