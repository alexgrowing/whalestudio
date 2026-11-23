import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCoverStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

theorem nonempty_fockData_pair :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s),
      Nonempty (FockData T0 T1 T2) := by
  intro p q r s T0 T1 T2
  obtain ⟨Om, h⟩ := GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover _ _ T0 (GlobalTheory.Mem.Osc.seqFock _)
  exact GlobalTheory.Osc.nonempty_fockData_iff.2 ⟨h.toOsc⟩

end GlobalTheory
