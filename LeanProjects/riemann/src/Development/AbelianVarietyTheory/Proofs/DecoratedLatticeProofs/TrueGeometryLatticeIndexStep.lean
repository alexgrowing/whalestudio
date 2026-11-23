import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

theorem locHom_eq_one_of_grpAt' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ¬ P q.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S P) :
    GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S P (· = q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

theorem relax_phi_mem_KO : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ g ∈ GlobalTheory.LevProd.relax J j hj α, ∀ i, GlobalTheory.LevProd.phi J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : GlobalTheory.LevProd.twAt J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact GlobalTheory.T.true_geometry_lattice_closed W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf
      ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.LevProd.twAt J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (GlobalTheory.LevProd.phi J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact GlobalTheory.T.levProd_phi_mem_KO_of_not_twAt W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
        change GlobalTheory.LevIdx.locHom (J'.G i).q _ _ x ∈ KO (J'.G i).k _
        rw [locHom_eq_one_of_grpAt' _ _ _ hv hx]
        exact one_mem _
    exact hle hsup
end GlobalTheory.LevProd
end
