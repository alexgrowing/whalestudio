import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters

namespace GlobalTheory

theorem weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair :=
  fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT

end GlobalTheory
