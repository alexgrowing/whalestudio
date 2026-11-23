import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieGalOfJumpsCardStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NOProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheorem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalRepRankTwo
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
namespace UpperTheory.GalS
theorem galClose_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), AutomorphicGaloisAdmissible D.nd D.naut :=
  fun hP hL D P => _root_.UpperTheory.GalS.Prod.automorphic_galois_admissible_of_theta_local_inputs hP (_root_.UpperTheory.GalS.mergeP'_alt hP.fin hL hP.gal hP.car hP.clo) hL D P
theorem trivialLocalCondition_of_inputs (_ : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (_ : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (_ : JumpsCard D.nd D.naut) (i : D.nd.Loc) : UnusedSlot55 D.nd D.naut i := trivial
theorem a_close_main : _root_.GlobalTheory.RowsAClose.mainTheorem := by
  intro hP hL D P hJ
  have hlab := _root_.GlobalTheory.TieLabAt.main_alt_alt hL D P
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hP.fin hP.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have haut := _root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hP.fin hL D P
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D P.T, haut.1, _root_.GlobalTheory.T.tieGal_of_jumpsCard_of_deRhamPotSemistable hP.berger hL D P hJ⟩
  have ha2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := _root_.UpperTheory.GalS.galClose_alt hP hL D P
  have ha7 : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D := _root_.UpperTheory.GalN.allCuspidalOpenBound_of_cuspU_character_choice hP.fin hP.gal hL D P
  refine ⟨hlab.1, GlobalTheory.RowClose.heckeSplitOne_of_charTied D P.cf P.C P.tp P.chr, htie0, ha2, han1, han2, ha5, ha7,
    _root_.UpperTheory.GalS.trivialLocalCondition_of_inputs hP hL D P hJ,
    haut.2⟩
end UpperTheory.GalS
end
