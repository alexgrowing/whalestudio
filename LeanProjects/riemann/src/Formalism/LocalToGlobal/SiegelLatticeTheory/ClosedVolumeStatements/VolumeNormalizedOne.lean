import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolSemiDirect
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolumeUnipotentOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolStabSW
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SupportDatum
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula
import Formalism.PeriodIntegrals.LocProdFormula
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

namespace Formalism.L2.SG.Closed

theorem volume_normalized_all : Formalism.L2.SG.Volumes.VolumeUnipotentAllCM := volume_unipotent_all_cm
theorem LevelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split
theorem volume_normalized_one : Formalism.L2.SG.Volumes.VolumeUnipotentOneFrom := volumeUnipotentOne

theorem VolumesFromSW_holds (hS0 : PI.VolFromSW.VolumeDegenerateFromSiegelWeil) : Formalism.L2.SG.Volumes.VolumesFromSW := by
  have hS := volume_stabilizer_from_siegel_weil
  unfold PI.VolFromSW.VolStabFromSW at hS
  unfold PI.VolFromSW.VolumeDegenerateFromSiegelWeil at hS0
  unfold Formalism.L2.SG.Volumes.VolumesFromSW
  unfold Formalism.MainNotions.UnusedSlot34.ForAllCM at *
  intros
  beta_reduce
  intro h1 h2
  constructor
  · apply hS <;> assumption
  · apply hS0 <;> assumption

theorem NormProd_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.NormProd D := by
  intro δ M hA x hx
  exact local_product_formula D.host.F D.host.E (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.conjF D.s.atP M
    (fun p => (hA p).1) x hx

theorem SupportLoc_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportLoc D := Formalism.L2.SG.Pf.localSupport_holds D

theorem SupportLemma_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportLemma D :=
  Formalism.L2.SG.SupportG.supportLemma_of_loc (SupportLoc_holds D) (NormProd_holds D)

theorem SupportVec_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportVec D := support_vector_all D

theorem DiffExists_holds {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : Formalism.L2.SG.LocVol.DiffExists v :=
  diffExists v

end Formalism.L2.SG.Closed
