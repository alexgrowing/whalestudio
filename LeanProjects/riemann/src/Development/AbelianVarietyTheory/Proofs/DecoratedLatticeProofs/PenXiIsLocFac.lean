import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.Fam.PenLoc

def penXi {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} (a : GeoAll W u) (n : Fin a.n)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank) (Fin ((I.rec7 l Z).sp.X (a.G n).s).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).Psi 1
    (((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β)
    ((a.G n).S.y0 (Fin B.R.t))

theorem penXi_isLocFac : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n),
    GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg (a.G n).s) (penXi a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col n
  have hR := (ha.tie row col).2
  letI := (a.G n).fld; letI := (a.G n).val; letI := (a.G n).top; letI := (a.G n).loc; letI := (a.G n).mea; letI := (a.G n).bor
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hid := (hR.idem n).1
  have hpf := GlobalTheory.LocMod.SymChainAt.place_facts (a.G n).q hid
  have hL : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L ∧
      ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun j hj => ⟨(ha.x j hj).sd, Set.ext (hat.pinX.xs j hj).2.2⟩
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, _, _, _, hpf.2, hid,
    GlobalTheory.SeeSaw.StdMatch.int_iff_up_mem (a.G n).q (a.G n).unit _ _ (hL _ (by omega)).1 (hL _ (by omega)).1 (hL _ (by omega)).2
      (hL _ (by omega)).2 ((a.G n).latX _ _) ((a.G n).latX _ _),
    GlobalTheory.LastTwoSteps.psi_mem_SB _ (Chain.ofType_regular _ _ _ _ _) _, (a.G n).cg_pen, fun _ => rfl⟩

end GlobalTheory.Fam.PenLoc
