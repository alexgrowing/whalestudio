import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.EtaleLiftToStrictLocalRingUniqueOnResidueField

namespace LateralTheory.E.ColimPf.Main

theorem Colim_of (hA : LateralTheory.E.ColimPf.Absorb) (hD : LateralTheory.E.ColimPf.Descend) : LateralTheory.E.SHLocPf.Colim :=
  LateralTheory.E.ColimPf.Colim_of hA LateralTheory.E.ColimPf.RigidPf.etale_lift_to_strict_local_ring_unique_on_residue_field hD

end LateralTheory.E.ColimPf.Main
