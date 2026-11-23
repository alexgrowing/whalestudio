import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelDataRayField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssembleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedSKAtWitnesses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem WPt.exists_recPinE_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) →
      Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  intro hA hW hR hL p K q hLT hZe hE
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.T.exists_spectral_data_compatible hA hW hL p K q hLT hZe
  obtain ⟨t, hK, hstd, hrd⟩ := GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie p.s K q hE
  obtain ⟨T, hTS, hTk, hcrd, hpin, hj, ⟨⟨hw⟩⟩⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses hL p K q S t hS hK
  have hp := GlobalTheory.Mem.Top.Bl.hostPins_wpt hR p.s K q
  subst hTS hTk
  obtain ⟨hd, -⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hA _ _ _ _ _ _ _ _ q.O.ex T.toTiedDataS hp q.x.pin.d3b
  exact ⟨⟨T, hpin, hj, ⟨hd⟩, hw⟩, ⟨⟨hS, hK, hcrd⟩, hE, hstd, hrd⟩⟩
end GlobalTheory.Mem.Top.Bl
end
