import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpCell
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed

namespace Formalism.L2.S.Pv.AmpFinal

open Formalism.MainNotions.S.Pv.LemmaJ

theorem rootCmp_of_parts (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) : RootCmp :=
  rootCmp_of Formalism.L2.S.Pv.AmpCell.cell_representation Formalism.MainNotions.S.Pv.AmpTrans.amplitude_transport hRJ hRH hOQ hRA

theorem ampUnif_of_parts (hAO : AmpOrbU) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of' hAO (rootCmp_of_parts hRJ hRH hOQ hRA) hNZ

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ampOrbU_of (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF) : AmpOrbU :=
  fun Cg cb Cu cT CT C0 => ⟨0, 1000, fun C' Cl _ hCl D large₂ =>
    Formalism.L2.SG.AmpOrbClosed.ampOrb0_of hJ hKD hKF D large₂ C' Cl Cg cb Cu cT CT C0 hCl⟩

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem amplitude_uniform_of_parts (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of_parts (ampOrbU_of hJ hKD hKF) hRJ hRH hOQ hRA hNZ

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem amplitude_uniform_of_orbit (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of_parts (fun Cg cb Cu cT CT C0 => ⟨0, 1000, fun C' Cl _ hCl D large₂ =>
    Formalism.L2.SG.AmpOrbClosed.ampOrb0 hJ hKD D large₂ C' Cl Cg cb Cu cT CT C0 hCl⟩) hRJ hRH hOQ hRA hNZ

end Formalism.L2.S.Pv.AmpFinal
