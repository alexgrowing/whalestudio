import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.VolMass

theorem volumes_eq_masses_of_unfold :
    (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D :=
  fun hU D hV =>
    have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie hV
    StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
      (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
        (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D))

end GlobalTheory.Mem.VolMass
