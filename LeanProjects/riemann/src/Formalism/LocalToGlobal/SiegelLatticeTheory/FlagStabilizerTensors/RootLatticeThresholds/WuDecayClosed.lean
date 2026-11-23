import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.Pf.WuDec

theorem besselMultOne_of_uniq (h : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.SG.LitS.BesselMultOne := by
  intro k r ε lam H _ _ σ z c u Wp _ _ π hl hds hz hT hc hπ B1 B2 h1 h2
  have h1' := (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B1).1 h1
  have h2' := (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B2).1 h2
  obtain ⟨a, b, hab, hlin⟩ := h k r ε lam H σ z c u Wp π hl hds hz hT hc hπ B1 B2 h1' h2'
  exact ⟨a, b, hab, fun v hv => hlin v hv⟩

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_closed (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hQK : Formalism.L2.SG.Pf.WFL.QuotProdK) (hHN : Formalism.L2.SG.Pf.WFL.LocHNProps) (hNU : Formalism.L2.SG.Pf.WFL.NUnimodLoc)
    (hS : LocScalarStep) (hU : LocUniqStep) : WuDecayOfGap :=
  wuDecay_of_gap Formalism.L2.SG.Closed.BesselNVGap_holds Formalism.L2.SG.Closed.CoefWeightedLoc_holds
    Formalism.L2.SG.Closed.WlocExists_holds (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_of_local_decomposition hDI hMU) (besselMultOne_of_uniq hMU)
    hQK hHN hNU hS hU

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem bessel_decay_of_gap (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hS : LocScalarStep) (hU : LocUniqStep) : WuDecayOfGap :=
  wuDecay_of_gap_closed hDI hMU Formalism.L2.SG.Closed.QuotProdK_holds Formalism.L2.SG.Pf.WFL.locHNProps_holds
    Formalism.L2.SG.Closed.NUnimodLoc_holds hS hU

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_scalar (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hMU : PI.BesselMapUniq.BesselMapUniq)
    (hS : LocScalarStep) : WuDecayOfGap :=
  bessel_decay_of_gap hDI hMU hS local_uniqueness_reduction

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecay_of_gap_jsz (hMU : PI.BesselMapUniq.BesselMapUniq) (hS : LocScalarStep) : WuDecayOfGap :=
  wuDecay_of_gap_scalar Formalism.L2.SG.BesselDiscreteSeries.decInf hMU hS

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem wuDecayOfGap_of_jsz (hMU : PI.BesselMapUniq.BesselMapUniq) : WuDecayOfGap :=
  wuDecay_of_gap_jsz hMU local_scalar_reduction

end Formalism.L2.SG.Pf
