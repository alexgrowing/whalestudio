import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankOneUnitaryAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTyzBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocGRankOneEqRcAt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace UpperTheory.GalN
open GlobalTheory.ParLawsBare GlobalTheory.RowTie GlobalTheory.NPin Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem tempered_of_true_cuspidal_alt (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7}
    {T : WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (h1 : RankOneUnitary T) : AllCuspidalOpenBound D.nd D.naut := by
  intro a π ha _ _ w
  have := GlobalTheory.CuspRep.host_isCMField D.host
  refine ⟨fun e => tempered_of_rank_le_one D T h1 a π e.le w, fun hu α hα => ?_⟩
  obtain ⟨-, hU, hS⟩ := _root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C
  obtain ⟨B, hB, e⟩ := hS a π w ha hu
  rw [e] at hα
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
  have k : OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E a _ (hU a π ha) w B hB b hb
  rw [Units.val_inv_eq_inv_val]
  exact k.inv (one_lt_q w)
theorem allCuspidalOpenBound_of_cuspU_character_choice : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), AllCuspidalOpenBound D.nd D.naut :=
  fun hF _ hL D P => _root_.UpperTheory.GalN.tempered_of_true_cuspidal_alt hF P.cg (_root_.GlobalTheory.TempGal.rankOneUnitary_of_charSide hF hL D P)
theorem allCuspidalOpenBound_of_parIn (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {rep Rw}
    (X : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw) : AllCuspidalOpenBound D.nd D.naut :=
  _root_.UpperTheory.GalN.tempered_of_true_cuspidal_alt hP.what₂.fin X.cg (_root_.GlobalTheory.ParLawsBare.rankOneUnitary_of_charSide X.T X.cg X.chr)
theorem par_laws_bare : _root_.GlobalTheory.ParLawsBare.mainTheorem := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  exact ⟨htie0, ha5, _root_.UpperTheory.GalN.allCuspidalOpenBound_of_parIn hP X, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩
end UpperTheory.GalN
end
end
