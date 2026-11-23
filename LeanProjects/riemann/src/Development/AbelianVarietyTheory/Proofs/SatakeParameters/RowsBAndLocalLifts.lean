import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitThetaCorrespondenceOfLocalPairings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowSizeOfUnitarySphericalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaOneGenusOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySphericalComponentOfReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm4OfRowsAStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoinStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsBClosing

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P →
    GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  intro hPr hL D P J hA h1 hpos
  have hRM : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hPr.fin hL D P hRM
  have hU : RowUnit S := GlobalTheory.RowUnitProof.rowUnit_of_isTrue hL D P hRM S hT
  have hPR : PairRead S := GlobalTheory.T.pair_reading_of_join hPr.bz hL D P J S hT hU
  have hpair : ∀ i, PairLift D.nd D.naut i :=
    GlobalTheory.SplitPairLift.main hPr.bz hPr.bern hPr.howe _ _ _ D.nd D.naut P.T S hLaws hU hPR
  have hIf := GlobalTheory.AdmIface.main D
  have hcheb : ChebSplit D.nd := (hIf.2.1 hA.a5).1
  have hsplit : ∀ i, SplitBC D.nd D.naut i := fun i =>
    GlobalTheory.RowTie.splitBC_of_galIso _ _ _ D.nd D.naut i (GlobalTheory.BCGal.main D hA.tie0 hA.a2 hA.temp i) hcheb hA.an2
  have hrep : ∀ i, RepOfLoc D.nd D.naut i := GlobalTheory.T.local_rep_of_reading_laws hL D P S hT hLaws
  have hbc : ∀ i, BCEx D.nd D.naut i := hIf.1 h1
  have horth : ∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := fun i => GlobalTheory.T.type_orthogonality_of_form hL D P i (J.form i)
  refine ⟨⟨?_, GlobalTheory.RowTie.split_theta_correspondence_of_local_pairings D hpair, GlobalTheory.T.adm4_of_rows_a hPr hL D P hRM hA,
    GlobalTheory.Proof.ThetaOneGenusOne.thetaOne_of_ties D hpos hpair horth hbc hsplit hrep⟩, fun i => ⟨hpair i, hsplit i, hrep i⟩⟩
  exact GlobalTheory.RowSizeClosing.rowSize_of_unitarySphericalComponent D
    (GlobalTheory.SplitRead.unitarySphericalComponent_of_reading hPr.bz _ _ _ D.nd D.naut P.T S hLaws hU)

end GlobalTheory.RowsBClosing
