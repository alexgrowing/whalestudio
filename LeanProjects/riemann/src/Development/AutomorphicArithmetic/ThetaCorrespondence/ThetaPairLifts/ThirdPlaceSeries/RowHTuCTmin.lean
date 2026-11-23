import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassEntry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc
theorem row_hTu_cTmin_alt : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
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
end
