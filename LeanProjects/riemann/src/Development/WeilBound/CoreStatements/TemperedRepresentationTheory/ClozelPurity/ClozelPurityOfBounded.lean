import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Purity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity

open NumberField GlobalTheory.CuspRep

namespace PositivityTheory.S2.Clozel

theorem clozelPurity_of_bounded : GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.ClozelPurity :=
  fun hB E _ _ _ a ha π h =>
    GlobalTheory.CompanionTheory.ClozelPurity.purity hB E a ha π (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ⟩) h

end PositivityTheory.S2.Clozel
