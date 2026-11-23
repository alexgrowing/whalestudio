import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsBAndLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowUnitOfIsTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoinStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairLiftOfHoweDualityBernstein
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalIso
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepOfReadingLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeOrthOfPinStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitarySphericalComponentOfReading
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalTypesDeterminedAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTailStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiOverO
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeStdTwCoverStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.One.M GlobalTheory.RowsBClosing
theorem UpperTheory.One.M.repGood_of_isTrue' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {S : Reading P.T} (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) :
    RepGood S := by
  intro i w hw Q
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w D w hw
  exact _root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q s _ (hT.rep i s hw Q)
namespace UpperTheory.One.M
theorem latticesB_closing_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P →
    _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  intro hPr hL D P J hA h1 hpos
  have hRM : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRM
  have hU : RowUnit S := _root_.GlobalTheory.RowUnitProof.rowUnit_of_isTrue_alt hL D P hRM S hT
  have hPR : PairRead S := _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit hPr.bz hL D P J S hT hU
  have hpair : ∀ i, PairLift D.nd D.naut i :=
    _root_.UpperTheory.One.M.pairLift_of_howeDuality_bernstein_alt hPr.bz hPr.bern _ _ _ D.nd D.naut P.T S hLaws hU hPR (_root_.UpperTheory.One.M.repGood_of_isTrue' P hT)
  have hIf := _root_.GlobalTheory.AdmIface.main_alt_alt D
  have hcheb : ChebSplit D.nd := (hIf.2.1 hA.a5).1
  have hsplit : ∀ i, SplitBC D.nd D.naut i := fun i =>
    _root_.UpperTheory.GalS.splitBC_of_galIso _ _ _ D.nd D.naut i (_root_.UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 D hA.tie0 hA.a2 hA.temp i) hcheb hA.an2
  have hrep : ∀ i, RepOfLoc D.nd D.naut i := _root_.GlobalTheory.T.repOfLoc_of_isTrue_laws hL D P S hT hLaws
  have hbc : ∀ i, BCEx D.nd D.naut i := hIf.1 h1
  have horth : ∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := fun i => _root_.GlobalTheory.T.type_orthogonality_of_form' hL D P i (J.form i)
  refine ⟨⟨?_, GlobalTheory.RowTie.split_theta_correspondence_of_local_pairings D hpair, _root_.GlobalTheory.T.archimedeanSignatureMatching_of_modules hPr hL D P hRM hA,
    GlobalTheory.Proof.ThetaOneGenusOne.thetaOne_of_ties D hpos hpair horth hbc hsplit hrep⟩, fun i => ⟨hpair i, hsplit i, hrep i⟩⟩
  exact GlobalTheory.RowSizeClosing.rowSize_of_unitarySphericalComponent D
    (_root_.GlobalTheory.SplitRead.unitarySphericalComponent_of_reading_alt hPr.bz _ _ _ D.nd D.naut P.T S hLaws hU)
end UpperTheory.One.M
end
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open UpperTheory.One.M
theorem exists_paired_point_of_thetaT_ne_zero (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (X : _root_.GlobalTheory.NRows.LinkedData hL D) :
    GlobalTheory.ThetaExh.ParamLaws D.nd D.naut ∧ GlobalTheory.SplitRead.XiOverO D.nd D.naut ∧ (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) ∧
      ∀ (i : D.nd.Loc) σ, (∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) →
        ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
          GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hH hD hL D X.P X.X X.agree
  have hRM : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D X.P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D X.P hRM
  have hU := _root_.GlobalTheory.RowUnitProof.rowUnit_of_isTrue_alt hL D X.P hRM S hT
  have hPR := _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit hP.bz hL D X.P J S hT hU
  exact ⟨GlobalTheory.RowLaws.paramLaws_of_tie X.P.T,
    _root_.GlobalTheory.ResLoc.xi_over_o_of_adm2 D X.P.cf X.P.C X.P.tp X.P.chr X.P.val (_root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hP.fin hL D X.P).1
      (_root_.UpperTheory.GalS.galClose_alt hP hL D X.P) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D.nd),
    _root_.UpperTheory.One.M.pairLift_of_howeDuality_bernstein_alt hP.bz hP.bern _ _ _ D.nd D.naut X.P.T S hLaws hU hPR (_root_.UpperTheory.One.M.repGood_of_isTrue' X.P hT),
    exists_pair_point D X.P.M X.P.H.hecke X.P.H.av X.P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D X.P)⟩
end GlobalTheory.ResLoc
end
end
end
