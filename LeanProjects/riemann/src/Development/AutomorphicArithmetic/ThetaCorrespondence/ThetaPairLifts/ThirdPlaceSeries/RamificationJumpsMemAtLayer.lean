import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GaloisRepDescendsAtRealPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemSatisfiesLocalProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemMonoOfColPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLambdaAdicDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.NRows.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
theorem exists_inputs_pinAt_jumpsCard_at_mem : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => ∃ I : _root_.GlobalTheory.NRows.LinkedInputs hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a I.P ∧ JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro prn prx hL
  have hA := _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_linked_data_pinned_at_layer prn hL) (_root_.GlobalTheory.T.serLoc_at_member_of_published_inputs prn hL)) (_root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_at_members_of_htCard prx.ht hL)
  refine _root_.GlobalTheory.NRows.AtLayer.atMem_mono_of_colPin (EvG.imp (EvG.inter GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices (_root_.GlobalTheory.T.adm8_and_lamUsed_of_readL_of_parameters prn prx)) fun _ _ _ _ _ hK => large₂.inter hK.1 hK.2) hA ?_
  rintro K B f T ⟨hS, hR⟩ kp w Z Wt p0 t nch n xd c ⟨ne⟩ _ cp ⟨⟨⟨X, hpin, -⟩, ser⟩, jumps⟩
  obtain ⟨-, -, -, -, -, hdef, -⟩ := hS kp T w Z
  have hr := hR kp w cp Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt t.r.Z X.X.given.params
  exact ⟨⟨X, { hypO := ne.large.1
               c1 := GlobalTheory.DesignBC.jointCond_of_definite _ hdef
               bc := _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt prn.bc prn.what₂.bern prn.gen prn.std hL _ X.P.T X.P.H.au X.P.cg X.P.au
               lam := hr.2
               isot := hr.1
               ser := ser
               typeNZ := _root_.GlobalTheory.T.galoisRep_descends_at_real_places prn.decay prn.howe prx _ _ _ _ X.X }⟩, hpin, jumps⟩
end GlobalTheory.NRows.AtLayer
end
end
end
