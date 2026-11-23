import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfGappedMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem row_hTu_cTmin : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT Bundle),
    Row Q Lk fun 𝒜 _ => R1.H_hTu (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) 𝒜 := by
  intro hU hG Q Lk
  refine Row.of_sel fun 𝒜 σ s => ?_
  refine Closed.of_class fun Fm _ h hle => ?_
  obtain ⟨κ, -, -, t⟩ := s Fm h.1.1.1
  have tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie := ⟨0, fun x _ hx i =>
    volTie_of_realTied _ (built_val _ _ _ _ _ _ _ _ (t x hx i).1).2.2.2.2.2.2.1.some⟩
  exact StandardLattice.HarishChandraReduction.tuSize_min Fm hle
    (family_property_mono tVol fun D hT => GenusMassVolumes.volume_eq_mass_rank_two D (StandardLattice.volumeMass_of_unfolding D (hU D hT)) (GenusMassVolumes.volume_mass_of_genus_rank D 2 hT (hG D)))
    (Formalism.MainNotions.GappedMultiplicityBounds.explicit_bound_family Fm)

end GlobalTheory.Fc

end
