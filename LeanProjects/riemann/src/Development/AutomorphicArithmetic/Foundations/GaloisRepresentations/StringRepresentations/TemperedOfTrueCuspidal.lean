import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace UpperTheory.GalN

open GlobalTheory.ParLawsBare GlobalTheory.RowTie GlobalTheory.NPin Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def TempCSDo (D : D7) : Prop := AllCuspidalOpenBound D.nd D.naut

theorem bareTemp (hP : PrN) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {rep Rw}
    (X : ParIn hL D cf rep Rw) : Formalism.MainNotions.SumRepresentations.adm7 D :=
  GlobalTheory.RowTie.admissible_of_rank_one_unitary D X.T (rankOneUnitary X.T X.cg X.chr)
    (fun a π ha hc hr w => rankTwo hP.what₂.fin hP.what₂.temp hP.what₂.clo X.T X.cg a π ha hc hr w)

theorem parLawsBare : type_of% @GlobalTheory.ParLawsBare.main := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (GlobalTheory.HeightCounting.Blocks.readsCusp hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  exact ⟨htie0, ha5, bareTemp hP X, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩

example : type_of% @GlobalTheory.T.parameter_laws_empty := parLawsBare

end UpperTheory.GalN
