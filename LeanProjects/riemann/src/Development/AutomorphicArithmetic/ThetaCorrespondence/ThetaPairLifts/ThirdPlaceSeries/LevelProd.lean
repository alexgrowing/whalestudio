import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsCompactRelaxStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocLevelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpPhiMemKOStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRelaxStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelEqUpInfStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
theorem GlobalTheory.LevProd.level_prod_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ Up : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), Up ≤ GfC _ ∧ IsCompact (Up : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ (H : ∀ i, Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) (φ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)), (∀ i, H i ≤ KO (J.G i).k _ ∧ MeasurableSet (H i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (H i).relIndex (KO (J.G i).k _) ≠ 0 ∧ (J.E i).wt j (α i) = ((((J.E i).m j (H i)).toReal⁻¹ : ℝ) : ℂ)) ∧ (∀ g ∈ Up, ∀ i, φ g i ∈ KO (J.G i).k _) ∧ (∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ Up, φ g = x) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  refine ⟨_root_.GlobalTheory.LevProd.upperLevelSubgroup a (j := j) (by omega), _root_.GlobalTheory.LevProd.upperLevelSubgroup_le_GfC a j (by omega), _root_.GlobalTheory.T.is_compact_upper_level_subgroup W hW u a ha hA j (by omega), fun t J hJ α => ?_⟩
  refine ⟨_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j (by omega) α, _root_.GlobalTheory.LevProd.localHomProduct J j (by omega), fun i => ⟨?_, ?_, ?_, _root_.GlobalTheory.LevProd.wt_eq_inv_measure_levelSubgroupAtPlace J j (by omega) α i⟩,
    _root_.GlobalTheory.T.true_geometry_lattice_step_value_alt W hW u a ha hA j (by omega) t J hJ, _root_.GlobalTheory.T.true_geometry_lattice_level_alt W hW u a ha hA j (by omega) t J hJ α,
    _root_.GlobalTheory.T.true_geometry_lattice_twist_alt W hW u a ha hA j (by omega) t J hJ α⟩
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.2
end
