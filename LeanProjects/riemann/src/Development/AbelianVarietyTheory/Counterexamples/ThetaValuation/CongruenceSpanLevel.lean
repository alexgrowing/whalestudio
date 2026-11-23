import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ArchimedeanGluing

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.Survey.CongruenceSpanLevel

open GlobalTheory.RunIn

theorem gamAt_of_lawsM {D : D7} (T : Core D) (h : LawsM T) : GamAt T :=
  (GlobalTheory.Survey.ArchimedeanCompatibility.gam_iff T).1 (GlobalTheory.Survey.ArchimedeanCompatibility.gam_of_laws T h)

end GlobalTheory.Survey.CongruenceSpanLevel
