import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Params
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

namespace GlobalTheory.PrimIn

structure Hypotheses2 : Prop where
  q1 : GlobalTheory.Hk3.HoweUnram
  q2 : GlobalTheory.Published.CuspRapidDecay
  q3 : GlobalTheory.Published.HarishChandraFinite
  q4 : GlobalTheory.Published.HarishChandraModules
  q5 : GlobalTheory.Published.DiscreteSeriesCover
  q6 : GlobalTheory.Published.CasselmanWallach
  q7 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  q8 : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  q9 : GlobalTheory.Published.DoublingMethod
  q10 : GlobalTheory.Published.UnramifiedDoublingGL
  q11 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  q12 : GlobalTheory.Published.GreenCuspidal
  q13 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  q14 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable

end GlobalTheory.PrimIn
