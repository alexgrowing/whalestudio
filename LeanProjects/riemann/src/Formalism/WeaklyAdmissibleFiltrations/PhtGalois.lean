import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Window
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.JumpsPFilAntitoneOfLe
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.RankOne
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExwaFiltrationNegOneEqSpanSingle
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.TrivCrys
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExLattice
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExistsPeriodRingDataHolds
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.WachCol
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.LiftGal
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.NegJumps
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.WindowCountIcoTelescope

namespace Formalism.WeaklyAdmissibleFiltrations

theorem pht_filphi : THWindow ∧ DimSum ∧ JumpsIcc ∧ SubTopBot ∧ RankOneWA ∧ ExWA :=
  ⟨hodgeDegreeWindow_and_multiplicitySum.1, hodgeDegreeWindow_and_multiplicitySum.2, jumpsIcc_and_subTopBot.1, jumpsIcc_and_subTopBot.2, rankOneWA,
    exWA⟩

theorem pht_galois : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe ∧ TrivCrys ∧ ExLattice ∧ ExPD ∧ WachCol :=
  ⟨finiteCocycles_properties.1, finiteCocycles_properties.2.1, finiteCocycles_properties.2.2.1, finiteCocycles_properties.2.2.2, trivialIsCrystalline_holds,
    existsStableLattice_holds, existsPeriodRingData_holds, cokernelLengthEqWach_holds⟩

theorem pht_lift : LiftGal ∧ NegJumps ∧ WindowCount :=
  ⟨liftGal, negativeJumpsSum_holds, windowCountAlt⟩

theorem pht_pc : DpcrisStable ∧ ExPC := dPotCrisStable_and_existsPotentiallyCrystallineData

end Formalism.WeaklyAdmissibleFiltrations
