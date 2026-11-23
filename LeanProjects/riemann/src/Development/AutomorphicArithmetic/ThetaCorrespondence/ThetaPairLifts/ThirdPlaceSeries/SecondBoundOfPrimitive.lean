import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitiveStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemMatrixGroupIdentityFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesCopyEmbeddingOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyRealStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem sb1l_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep := by
  intro hPr hSer hL cDep
  refine (StepW.and (_root_.GlobalTheory.MtId.exists_matrix_input_identity_frame_of_inputs hPr) (StepW.of_all fun _ _ _ _ _ _ _ h => h)).trans
    (StepW.of_all fun K B f T w hK hF H P x l => ?_)
  obtain ⟨N, hN, hser⟩ := _root_.GlobalTheory.T.series_copy_embedding_of_cmDatum_alt hPr hSer hL hK hF H.2 x l
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb, hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l.toLI N
  obtain ⟨m, hm⟩ := H.1 P x'
  obtain ⟨b⟩ := hser x' l' ho hrow hPq hS hSb hhL heig hθ hR hcG hgeo m hm
  exact ⟨x', ⟨{ toLI := { l' with mt := m }, b := b }⟩, listSt_oTw cDep x N hN x' ho hLc⟩
end GlobalTheory.HeightCounting.Up.SeriesStep
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesExistList_of_inputs_serN : (_root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | exact _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt <;> assumption)
end
end
