import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeTwistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem GlobalTheory.LevProd.level_prod : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ Up : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), Up ≤ GfC _ ∧ IsCompact (Up : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : QJ a t), J.Reads → ∀ α : J.Ch j, ∃ (H : ∀ i, Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) (φ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)), (∀ i, H i ≤ KO (J.G i).k _ ∧ MeasurableSet (H i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (H i).relIndex (KO (J.G i).k _) ≠ 0 ∧ (J.E i).wt j (α i) = ((((J.E i).m j (H i)).toReal⁻¹ : ℝ) : ℂ)) ∧ (∀ g ∈ Up, ∀ i, φ g i ∈ KO (J.G i).k _) ∧ (∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ Up, φ g = x) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  refine ⟨GlobalTheory.LevProd.Up a (j := j) (by omega), GlobalTheory.LevProd.Up_le a j (by omega), GlobalTheory.T.true_geometry_lattice_step_relation W hW u a ha hA j (by omega), fun t J hJ α => ?_⟩
  refine ⟨GlobalTheory.LevProd.H J j (by omega) α, GlobalTheory.LevProd.phi J j (by omega), fun i => ⟨?_, ?_, ?_, GlobalTheory.LevProd.wt_eq J j (by omega) α i⟩,
    GlobalTheory.T.true_geometry_lattice_step_value W hW u a ha hA j (by omega) t J hJ, GlobalTheory.T.true_geometry_lattice_level W hW u a ha hA j (by omega) t J hJ α,
    GlobalTheory.T.true_geometry_lattice_twist W hW u a ha hA j (by omega) t J hJ α⟩
  · exact (GlobalTheory.T.true_geometry_lattice_transport W hW u a ha hA j (by omega) t J hJ α i).1
  · exact (GlobalTheory.T.true_geometry_lattice_transport W hW u a ha hA j (by omega) t J hJ α i).2.1
  · exact (GlobalTheory.T.true_geometry_lattice_transport W hW u a ha hA j (by omega) t J hJ α i).2.2
