import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AmplitudeOrbitalIntegral
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.BesselSchurOfDec
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfUniqGap
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.AutomorphicTheory.RankOneTori.KDense

namespace CompanionTheory.Lime.BM

theorem uniqGap_of_bmu (h : CompanionTheory.Bmu.BesselMapUniqGap) : UniqGap := h

theorem wuDecayOfGap (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap h

theorem besselOfW (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.L2.SG.LocWSOf.BesselOfW :=
  Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap h

theorem ampUnif (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.L2.S.Pv.AmpOrbCoef.BM.ampUnif_gap h
    fun k r ε lam H _ _ _ σ hl hσ v hv Ws hWs e he => Formalism.MainStatements.RankOne.KD.kDense k r ε lam H σ hl hσ v hv Ws hWs e he

end CompanionTheory.Lime.BM
