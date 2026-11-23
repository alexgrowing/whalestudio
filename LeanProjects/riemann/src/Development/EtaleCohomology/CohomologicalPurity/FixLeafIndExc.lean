import Development.EtaleCohomology.CohomologicalPurity.OffContBasicPfR
import Development.EtaleCohomology.CohomologicalPurity.ResLECompIsoOpenInfPreimageHomNaturality
import Development.EtaleCohomology.CohomologicalPurity.OffContLocKnxPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHsContPfFive
import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdExcPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf

namespace LateralTheory.Fix.LeafIndExc
open LateralTheory.CohomologicalPurity

theorem bd : LeafBd :=
  Bd.goal_of Bd.LeafMono_of Bd.LeafPush_of Bd.LeafGood_of Bd.LeafDelta_of Bd.LeafExact_of
    (Bd.LeafImg_of (Bd.LeafImgHom_of Bd.LeafGen_of))

theorem exc : LeafExc :=
  LeafExc_of (LeafExcFormal_of EtaleExcIdent LeafExcDeg_of)
    (LeafExcSheaf_of (LeafFreeCok_of_inj LeafFreeCokInj_of) LeafSurjGeo_of LeafInjGeo_of)

theorem offCont : LeafOffCont :=
  leafOffCont_of offContBasic_of (etale_purity_continuity_off_closed_of_local_and_chase OffContLoc_of OffChaseGeo_full)

theorem intersectionNumber_baseChange : LeafIndExc :=
  leafIndExc_of (leafNbhdExc_of exc) (leafHsCont_of' bd exc offCont)

end LateralTheory.Fix.LeafIndExc
