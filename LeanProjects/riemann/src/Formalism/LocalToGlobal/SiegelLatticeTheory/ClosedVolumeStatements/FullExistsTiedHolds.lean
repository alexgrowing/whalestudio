import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FixedDecomposition
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurNFCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullTied
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HostUnram
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDualGen
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocHaarRR
import Formalism.PeriodIntegrals.LocHaarRR
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PinHostLoc
import Formalism.PeriodIntegrals.PinHostLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormExpSatHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdCellOffCHoldsOfVol

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Closed

theorem FinLeviC_holds : Formalism.L2.SG.Pf.FinLeviC := Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds

theorem FoldOKC_outright : FoldOKC := FoldOKC_holds FinLeviC_holds

theorem OOLintSumC_holds : Formalism.L2.SG.Pf.OOLintSumC :=
  Formalism.L2.SG.Pf.ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

theorem OOIntAllC_outright : OOIntAllC := OOIntAllC_holds OOLintSumC_holds

theorem AbsConvC_outright : AbsConvC := AbsConvC_holds OOLintSumC_holds

theorem IdCellOffC_outright : IdCellOffC := IdCellOffC_holds Formalism.L2.SG.Pf.idOffConjC_holds Formalism.L2.SG.Pf.idOffLiftC_holds

theorem KppOffC_holds : Formalism.L2.SG.RowsConc.KppOffC :=
  Formalism.L2.SG.FixedDecomposition.kppOffC_of_steps0 FoldOKC_outright FundExistsC_holds OOIntAllC_outright LemmaVC_holds
    (Formalism.L2.SG.FixedDecomposition.covariantRepZero_of_lemmaV AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds)
    schurNFC

theorem NormExpSat_of_decay {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hWX : Formalism.L2.SG.WuDecay.WuDecay X)
    (Y : Full X) (u u' : D.what₂.Word)
    (hA : AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u'))
    (hAbs : AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')) :
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') := by
  have hF := FundExistsC_holds D X Y u u'
  have hO : ∀ w, Formalism.L2.SG.WuDecay.FoldOK X w Y.hK :=
    fun w => FoldOKC_outright D X Y w (level_subgroup_properties X) hWX
  have hI := OOIntAllC_outright D X Y u u' (hO u) (hO u') hF
  exact Formalism.L2.SG.NormCut.normExpSatC'_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u u' hI hA
    (OOFundIndepC_holds D X Y u u' hF hI) hAbs

theorem LocHaarC_holds : Formalism.L2.SG.Pf.LocCP.LocHaarC := by
  intro D _ p
  obtain ⟨μ, h1, h2, h3⟩ := local_haar_real_real _ _ _ _ (D.s.atP p) (Formalism.L2.SG.Pf.LocCP.reduced p)
  refine ⟨μ, h1, h2, ?_⟩
  have hR : Formalism.L2.SG.Pf.LocCP.RR p = PI.LocHaarRR.RR (D.s.atP p) := by
    unfold Formalism.L2.SG.Pf.LocCP.RR PI.LocHaarRR.RR
    cases (D.s.atP p).split <;> rfl
  rw [hR]
  exact h3

theorem PinHostC_holds : Formalism.L2.SG.Pf.LocCP.PinHostC :=
  fun D hT p i hi => prime_quotient_unit _ _ _ _ (D.s.atP p) D.host.g D.host.g_prime D.host.g_ne i hi
    (Formalism.L2.SG.Pf.HostUnramP.hostUnramG D hT p i hi)

theorem LocDualGenC_holds : Formalism.L2.SG.Pf.LocCP.LocDualGenC := fun D _ p => local_dual_generation _ _ _ _ (D.s.atP p)

theorem LocCTied_holds : Formalism.L2.SG.Pf.FullLocalDualAgreement.LocalDualAgreement :=
  Formalism.L2.SG.Pf.FullLocalDualAgreement.locCTied_of' (Formalism.L2.SG.Pf.FullLocalDualAgreement.locDualC_of' LocDualGenC_holds PinHostC_holds)
    LocHaarC_holds

theorem FullExistsTied_holds (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (hT : Formalism.L2.SG.Pf.LocCP.LocTied D) : Nonempty (Full X) :=
  Formalism.L2.SG.Pf.fullExists_tied TRExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold LocCTied_holds D X
    (level_subgroup_is_group X) hT

end Formalism.L2.SG.Closed
