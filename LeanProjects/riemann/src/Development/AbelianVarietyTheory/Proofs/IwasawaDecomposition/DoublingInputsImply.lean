import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Hypotheses3OfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatMultEq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem

theorem hypH_of_rowRatW : PrM → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → RowRatW → HypH :=
  fun m hm dc cw ws sw e1 e2 ud bz so rs r =>
    hypH_of dc (GlobalTheory.hypotheses3_of_siegelWeil GlobalTheory.Hk3.howeUnram_holds m.m3 m.m4 hm dc cw ws sw e1 e2 ud bz m.m14 so) rs GlobalTheory.Published.HeckeLPartialContinuation_holds
      (GlobalTheory.Mem.R3.Rw.MultAt.atDat_multEq m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m8 m.m9 m.m10 m.m11 m.m12 m.m13 m.m14) r

end GlobalTheory.Mem
