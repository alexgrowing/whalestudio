import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw

namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
