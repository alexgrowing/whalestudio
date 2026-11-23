import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfGenusClasses
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem genus_class_mass : PI.UJClassMass2.UJClassMass := _root_.unitary_class_mass_hermitian

theorem classMass_of_D7 (D : D7) : ClassMass D := class_mass_of_genus_classes genus_class_mass D

theorem definite_class_decomposition (D : D7) : DefClassDecomp D := defClassDecomp_of_UJ genus_class_mass D

theorem definite_volume_mass (D : D7) (hT : VolTie D) (hG : GenusMassStd D) : DefiniteVolumeEqMass D :=
  volume_mass_of_genus_classes D hT hG genus_class_mass

theorem definite_volume_mass_of_tie (D : D7) (hG : GenusMassStd D) : Formalism.MainNotions.RT.GenusMassUnderVolume D :=
  Formalism.MainNotions.RT.genus_mass_of_class_decomposition D hG (definite_class_decomposition D)

theorem volume_mass_of_genus_rank (D : D7) (n : ℕ) (hT : VolTie D) (hG : GenusMassAt D n) : volumeAtLevelZero D n :=
  volume_mass_of_class_data D n hT hG (class_number_finite_rank D n) (classMassAt_of D (classMass_of_D7 D) n)

theorem volume_mass_all_ranks (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (n : ℕ) : volumeAtLevelZero D n :=
  volume_mass_of_genus_rank D n hT (genusMassAt_of D hG n)

theorem link_theorem_two : Link2 := Link2_of_UJ genus_class_mass

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.ConcTop

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_independence (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞)
    (hW : WeilSiegelCM)
    (hV : RowRec 𝒞 VolSigIndep)
    (hHC : RowRec 𝒞 HCFormalDegree)
    (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd)
    (hN : RowCount 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.classMass_of_D7 hR) hHC hL hG hN

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_class_count (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_independence 𝒞 C3 hC3 hR hW hV hHC hL hG (rowCount_of_clsTie hX)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
