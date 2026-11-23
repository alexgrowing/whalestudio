import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPolEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolExStOfPublished

open GlobalTheory.ShFam GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem sysExSt_of_toroidal (hSieg : GlobalTheory.Published.SiegelToroidalIntegral)
    (hFan : GlobalTheory.Published.ToroidalChartsForFan) : SysExSt :=
  sysEx_of_polEx (polExSt_of_siegel_of_fan hSieg hFan)

end GlobalTheory.TorRef
