import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenXiIsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowFamilyValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem pen_locFac : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat n j hj hj2
  have hstd := hat.pinX.std
  have row : ∀ t, RowCh (pk W) (lvP W) u a.g t := fun t =>
    ⟨fun _ _ => 0, fun _ _ _ => 0, fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hstd _ _).some,
      fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hstd _ _).some, fun _ => 0, fun _ _ => 0⟩
  have col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) :=
    fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
        Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s := by omega
  obtain ⟨c, hc, hmatch⟩ := GlobalTheory.T.true_geometry_row_family_value W hW u a ha hat row col n hj
  refine ⟨c, hc, fun t J hJ α γ => ⟨penXi a n, penXi_isLocFac W hW u a ha hat row col n, fun P hP z => ?_⟩⟩
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hh : ∀ b, (I.idx (W.P.I.tup t)).h (a.G n).s b P = 1 := by
    rw [(hW.tr.tw (W.P.I.tup t)).2]
    exact fun b => GlobalTheory.SeeSaw.StdMatch.twSt_h _ _ _ _ _ _ b P hPv
  rw [← hmatch t J hJ α γ P hP z]
  unfold GlobalTheory.QTw.locXi
  rw [dif_neg (by omega), dif_pos (by omega), hh]

end GlobalTheory.Fam.PenLoc
