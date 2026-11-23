import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeRelaxedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section

namespace GlobalTheory.PenBridge

set_option maxHeartbeats 1000000 in

theorem pen_bridge : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∃ U0 : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), U0 ≤ GfC _ ∧ IsCompact (U0 : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : QJ a t), J.Reads → ∀ α, J.A.U j (J.ι j α) ≤ U0 ∧ (J.A.U j (J.ι j α)).relIndex U0 = ∏ i, (GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i)))).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj
  obtain ⟨U0, hle, hcpt, H⟩ := GlobalTheory.T.true_geometry_lattice_relaxed W hW u a ha hTr j hj
  refine ⟨U0, hle, hcpt, fun t J hR α => ?_⟩
  obtain ⟨hMv, hK, hα⟩ := H t J hR
  obtain ⟨c, hc, hmem⟩ := hα α
  have hsub : J.A.U j (J.ι j α) ≤ U0 := fun g hg => ((hmem g).1 hg).1
  refine ⟨hsub, ?_⟩
  have hcKO : ∀ i, c i ∈ KO (J.G i).k _ := fun i => (J.E i).le ((J.G i).s + 1) 0 rfl (hc i)
  have hCK : ∀ i, (GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i)))) ≤ KO (J.G i).k _ := fun i =>
    (GlobalTheory.PenVol.cosStab_le _ _ _).trans ((J.E i).le ((J.G i).s + 1) 0 rfl)
  have hJK : ∀ i, ((GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))))).comap (MulAut.conj (c i)).toMonoidHom ≤ KO (J.G i).k _ := by
    intro i x hx
    have hx' : c i * x * (c i)⁻¹ ∈ KO (J.G i).k _ := hCK i hx
    have e : x = (c i)⁻¹ * (c i * x * (c i)⁻¹) * c i := by group
    rw [e]
    exact (KO _ _).mul_mem ((KO _ _).mul_mem ((KO _ _).inv_mem (hcKO i)) hx') (hcKO i)
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hinj : Function.Injective fun i => (J.G i).q.v := GlobalTheory.T.injective_QJ_G_q_v W hW u a ha hTr t J hR
  have hidx := GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi (rd J j hj) U0 (J.A.U j (J.ι j α)) (fun i => KO (J.G i).k _)
    (fun i => ((GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))))).comap (MulAut.conj (c i)).toMonoidHom) hJK ?img ?onto ?mem
  · rw [hidx]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact relIndex_comap_conj _ _ (hcKO i)
  case img =>
    intro g hg i
    show rdAt J j i (step_before_last_eq_s_succ J hj i) g ∈ _
    rw [rdAt_apply, toSum0_mem_KO_iff]
    exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (J.G i).q _ (frJ J j i (step_before_last_eq_s_succ J hj i)) (a.g.x j).L (plF J) ⟨i, rfl⟩
      (intIn_frJ J j i _) g (hMv g hg) _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
  case onto =>
    intro x hx
    obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices ((I.rec7 l Z).sp.X j) (a.g.x j).L hsd (fun i => (J.G i).k) (fun i => (J.G i).q)
      _ (fun i => frJ J j i (step_before_last_eq_s_succ J hj i)) hinj (fun i => intIn_frJ J j i _)
      (fun i => (toSum0 (J.G i).k _).symm (x i)) (fun i => by rw [← toSum0_mem_KO_iff]; simpa using hx i)
    refine ⟨g, hK g hg, funext fun i => ?_⟩
    show rdAt J j i (step_before_last_eq_s_succ J hj i) g = x i
    rw [rdAt_apply, ← (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgx i)]
    simp
  case mem =>
    intro g
    rw [hmem g]
    rfl

end GlobalTheory.PenBridge

end
