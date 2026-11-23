import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeTransport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem loc_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i
  have hs := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj
  have hjm : j < B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  have hle : _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ :=
    prX_le_KO_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep (hL.int _ _ _)
  have hreg := (J.E i).reg
  have hJo : IsOpen ((((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
      (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k)) :=
    (hreg.2.2 _ _ _).1
  set g₀ := (J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' hs) (α i) with hg₀
  have hOo : IsOpen {w : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k |
      g₀⁻¹ * w * g₀ ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
        (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J} :=
    hJo.preimage (by fun_prop)
  have hpo : IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := by
    refine GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [one_mem]) ?_
    intro z hz hzO
    exact GlobalTheory.StepData.mem_Cgrp.2 ⟨hz, hzO⟩
  refine ⟨hle, hpo.measurableSet, ?_⟩
  have hc := GlobalTheory.SplitFlip.isCompact_KO (k := (J.G i).k) (n := XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
  haveI : CompactSpace (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) := isCompact_iff_compactSpace.1 hc
  have ho' : IsOpen (((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _) : Subgroup _) : Set (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j))) :=
    hpo.preimage continuous_subtype_val
  haveI : Finite (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ⧸ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)) :=
    ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).quotient_finite_of_isOpen ho'
  haveI : ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero
end GlobalTheory.LevProd
end
end
