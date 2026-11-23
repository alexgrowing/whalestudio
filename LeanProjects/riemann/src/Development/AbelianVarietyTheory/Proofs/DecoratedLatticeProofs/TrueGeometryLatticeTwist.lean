import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

open scoped Pointwise in

theorem GlobalTheory.LevProd.level_eq_up_inf : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ GlobalTheory.LevProd.Up a j hj ∧ ∀ i, GlobalTheory.LevProd.phi J j hj g i ∈ GlobalTheory.LevProd.H J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hT' j hj t J hJ α g

  have hle : ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j),
      GlobalTheory.LevProd.relax J j hj α ≤ GlobalTheory.LevProd.relax J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨GlobalTheory.T.true_geometry_lattice_index_value W hW u a ha hT' j hj t J hJ α t' J' hJ' α' x hx, ?_⟩, ?_⟩
    · exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
    · exact (Subgroup.mem_pi _).2 fun i _ => GlobalTheory.T.true_geometry_lattice_index_step W hW u a ha hT' j hj t J hJ α t' J' hJ' x hx i
  have hUp : GlobalTheory.LevProd.Up a j hj = GlobalTheory.LevProd.relax J j hj α := by
    have hex : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
    unfold GlobalTheory.LevProd.Up
    rw [dif_pos hex]
    exact le_antisymm (hle _ _ hex.choose_spec.choose_spec.1 _ _ _ hJ α) (hle _ _ hJ α _ _ hex.choose_spec.choose_spec.1 _)
  rw [hUp]
  have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.LevProd.twAt J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
  constructor
  · intro hg
    have hf := GlobalTheory.T.true_geometry_lattice_measure_value W hW u a ha hT' j hj t J hJ α g hg
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hg, ?_⟩, ?_⟩, hf⟩
    · exact ((hJ.is.U j (by omega) _ g).1 hg).1
    · exact (Subgroup.mem_pi _).2 fun i _ => GlobalTheory.T.true_geometry_lattice_measure_step W hW u a ha hT' j hj t J hJ α i (hf i)
  · rintro ⟨hr, hH⟩
    have hs := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hr).1).1
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) * (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.LevProd.twAt J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    have hn' : n ∈ J.A.U j (J.ι j α) := by
      refine GlobalTheory.T.true_geometry_lattice_conjugate W hW u a ha hT' j hj t J hJ α n hn fun i => ?_
      have h1 := GlobalTheory.T.true_geometry_lattice_measure_value W hW u a ha hT' j hj t J hJ α x hx i
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      simpa using (Subgroup.mul_mem_cancel_left _ h1).1 h2
    exact mul_mem hx hn'
