import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_existence_everywhere : Always fun U x => ArchEx U x := by
  first | exact @GlobalTheory.FlatCore.archEx_always | exact GlobalTheory.FlatCore.archEx_always | (intros; apply GlobalTheory.FlatCore.archEx_always <;> assumption)
