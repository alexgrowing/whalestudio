import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LinkNOfGd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalTypeDeterminedAtAllPrimes
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OverNEOfNEb
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtraBoundOfTwistingEigenFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTailStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.At23OfAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.NLink
def CutGivesAlt : Prop := ∀ (D : D7) (nch : NChoice D), _root_.UpperTheory.GalC.GaloisPreconditions D nch → Tie4 D →
  ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchTr c nch) ∧ Tie4 (cut D c)
theorem linkN_of_twGood_galoisPreconditions (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) {eps : ℝ} (Fm : FamP eps) (hTw : TwGood Fm)
    (hF : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.UpperTheory.GalC.GaloisPreconditions (Fm.D x i) (Fm.ex x hx i).nch ∧ Tie4 (Fm.D x i)) : LinkN Fm := by
  classical
  obtain ⟨C, CT, hC, hEx⟩ := _root_.GlobalTheory.T.exists_const_tieChi_bound_of_facts hP
  have key : ∀ x (i : Fm.Ix x), ∃ c : CutD (Fm.D x i), ∀ hx : Fm.x1 < x, c.Good ∧
      _root_.GlobalTheory.NFacts.NormChoiceFacts (cut (Fm.D x i) c) (nchTr c (Fm.ex x hx i).nch) ∧ Tie4 (cut (Fm.D x i) c) := fun x i => by
    by_cases hx : Fm.x1 < x
    · obtain ⟨c, h⟩ := hG _ _ (hF x hx i).1 (hF x hx i).2
      exact ⟨c, fun _ => h⟩
    · exact ⟨CutD.all _, fun h => absurd h hx⟩
  choose c hc using key
  have hFF : _root_.GlobalTheory.NLink.FactsFAlt (gd Fm c) C CT := fun x hx i =>
    ⟨(hc x i hx).2.1, hEx _ _ (hc x i hx).2.1 (hc x i hx).2.2⟩
  refine linkN_of_gd Fm c (fun x hx i => ⟨(hc x i hx).1, ?_, (hF x hx i).1.what₂.rank _⟩)
    (GlobalTheory.T.linkN_along_family_of_localBounds _ (_root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three hP _ C CT hC (twGood_gd Fm c hTw) hFF (_root_.UpperTheory.N.at23_family_alt hP _)))
  have p := (hF x hx i).1
  exact GlobalTheory.T.goodPointMultiplicityLeRank_proof _ _ p.Conclusion1.2.2 p.z p.adm.2.2 p.c2
theorem linkN_of_boundAtTwoThree_slot (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition)
    (hE : GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h23 : _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  exact _root_.UpperTheory.GalC.linkN_of_twGood_galoisPreconditions hP hG Fm hc.1.2 fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
theorem linkedAt_linkN_of_boundAtTwoThree (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
    (h1 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h3 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and r3, ?_⟩
  refine _root_.UpperTheory.GalC.linkN_of_boundAtTwoThree_slot hP hG _ _ ?_ ?_
  · exact GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩) e3
open Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc in
theorem final_of_alt (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (prN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hX : _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility)
    (dzs : GlobalTheory.Published.DepthZeroSupport) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
    (hF : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ nch _ _ => _root_.UpperTheory.GalC.GaloisPreconditions (w.D Z) nch)
    (hAt : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  have hW : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)).s :=
    GlobalTheory.T.witnesses_pass_along_set_division _ (_root_.GlobalTheory.NLink.Final.slot_mv_extension_with_list_geo_cl hL cDep anyGeometry)
  have hTf := _root_.GlobalTheory.T.tieChi_at_members_of_depthZero hX.ht prN dzs hL
  have hTr := (_root_.GlobalTheory.Mem.AtPtTransport.atMem_at_wit_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hW
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ e => ⟨e.1⟩)).2
  exact _root_.UpperTheory.GalC.linkedAt_linkN_of_boundAtTwoThree hP hG hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry))
    (hTr (fun D nch => _root_.UpperTheory.GalC.GaloisPreconditions D nch ∧ Tie4 D) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z hF hTf)) hAt
end UpperTheory.GalC
end
end
