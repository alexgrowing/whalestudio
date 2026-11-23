import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlgOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCarAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabNFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfNSA
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDensePf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu

namespace Formalism.L2.SG.Pf.RegroupPf

theorem foldReadyX_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized →
    Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X :=
  fun _ X _ => Formalism.L2.SG.PoincareInHH.Cut.foldReadyX_holds X

theorem neatKu_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK :=
  fun _ X Y u _ => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u Y.hK
    (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u Y.hK)

theorem nDense_RG : NDense := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation

theorem slabCoverC_holds : Formalism.L2.SG.Pf.Slab.SlabCoverC := Formalism.L2.SG.Pf.SlabCoverPf.slab_covering_of_strong_approx nDense_RG Formalism.L2.SG.Pf.nilradical_conj_level'
  (fun _ X u => Formalism.L2.SG.Pf.Level.ratLevi_holds X u) (fun _ X => Formalism.L2.SG.Pf.psiDd_holds X)

theorem regroupC_all : Formalism.L2.SG.Pf.Slab.RegroupC := regrouping_of_neatness (nStrongApproxC_of nDense_RG)
  (orbit_algebra_of_stabilizer term_carrier_holds (stabilizer_of_neat_level neatKu_K2Level)) slabCoverC_holds foldReadyX_K2Level neatKu_K2Level

end Formalism.L2.SG.Pf.RegroupPf
