import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.GoodIdemTie

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem idemTie_of_tameTie (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) : GlobalTheory.DimPartsCompare.IdemTie D om :=
  hT.idemTie hG.green

theorem coeff_eq_mapDomain (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) :
    D.ntypes.e0.coeff =
      Finsupp.mapDomain GlobalTheory.DimPartsCompare.pull (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.goodIdem (H := D.host) om).coeff := by
  rw [Finsupp.ext_iff, GlobalTheory.DimPartsCompare.pull_bijective.2.forall]
  simp only [Finsupp.mapDomain_apply GlobalTheory.DimPartsCompare.pull_bijective.1]
  exact idemTie_of_tameTie hG D om hT

end GlobalTheory.GoodIdemTie

end
