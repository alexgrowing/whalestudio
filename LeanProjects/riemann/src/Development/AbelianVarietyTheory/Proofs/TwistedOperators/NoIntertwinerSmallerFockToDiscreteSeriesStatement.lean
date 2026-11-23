import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.SmallerSource.no_map_smaller_source | exact GlobalTheory.SmallerSource.no_map_smaller_source | (intros; apply GlobalTheory.SmallerSource.no_map_smaller_source <;> assumption)
