import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

namespace GlobalTheory.Ex

theorem hv_holds : GlobalTheory.Ex.HV :=
  GlobalTheory.TestFibre.laws_all GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1

end GlobalTheory.Ex
