import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemInputsAtThirdPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerRest
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointStageEigenspaceSpan
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemPartitionLambda
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RhoBarOfRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRowsStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
namespace PointStatements
section Loc
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
end Loc
theorem aux_residual_aux42_prvZ_of_inputs {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hc : GlobalTheory.Published.HarishChandraFinite)
    (dec : GlobalTheory.Published.CuspRapidDecay) (I : _root_.GlobalTheory.NRows.LinkedInputs hL D) (hJ : JumpsCard D.nd D.naut) :
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ SumRepresentations.Conclusion42 D ∧ SumRepresentations.ConclusionZ D := by
  have R : _root_.GlobalTheory.NRows.PointConditions' D := _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard hPr hc dec hL D I hJ
  have h1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b
  exact ⟨h1.1, _root_.GlobalTheory.HeightCounting.Up.PointStatements.residualIrreducibleGood_of_inputs hL D I R, h1.2.2, (SumRepresentations.multiplicity_statement_iff_reduced D I.isot h1.2.2).2 (_root_.GlobalTheory.T.reducedMultiplicity_of_inputs hL D I R)⟩
end PointStatements
open PointStatements in
theorem ptSt_of_inputs_geometric_compat : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL := by
  intro hP hX hL
  have h := allSt_and (allSt_and (allSt_and (_root_.GlobalTheory.T.eventually_nonempty_inputs_of_level_c hL hP hX) (_root_.GlobalTheory.HeightCounting.JumpsSt.locComp_of_isRc_classMapD_cenLoc hL hP hX.ht))
    (_root_.GlobalTheory.HeightCounting.Up.eventually_eigSpan_of_levelC hL hP)) (_root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat hP hX)
  refine allSt_mono (fun K B f T w P x H l => ?_) h
  obtain ⟨⟨⟨hI, hJ⟩, hE⟩, hS⟩ := H
  refine _root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_mono_withLoc ?_ (_root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_and (_root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_and (hI l) (hJ l)) (hE l))
  rintro L ⟨⟨hI', hJ'⟩, hE'⟩
  exact ⟨fun ho => _root_.GlobalTheory.HeightCounting.Up.PointStatements.aux_residual_aux42_prvZ_of_inputs hP.what₂ hP.hc hP.decay (hI' ho).some (hJ' ho), hE', hS.1⟩
end GlobalTheory.HeightCounting.Up
end
end
end
