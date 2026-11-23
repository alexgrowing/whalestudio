import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.KomExist

theorem even_rankX {D : D7} (j : ℕ) (hj : j ≤ D.R.m) : Even (D.sp.X j).rank := by
  rw [Formalism.L2.Forms.rankN D j hj]
  show Even (D.R.k + j * (D.R.t + 1))
  obtain ⟨c, hc⟩ := D.R.t_odd
  exact D.R.k_even.add (Even.mul_left ⟨c + 1, by omega⟩ j)

theorem kom_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (pk W).ψ _ _ (chrK W t j) (chrK W t j) (kom t j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ haT
  have hL := hW.pk.bot.hyp.2.2.2.1.lev
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists (I.rec7 l Z)
  have key : ∀ (t : W.P.T) j, j < B.R.m → ∃ om : Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
      IsWeilDatumO (pk W).ψ _ _ (chrK W t j) (chrK W t j) om := by
    intro t j hj
    have hH := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t ⟨j, hj⟩
    exact hE _ _ (pk W).ψ _ _ haT.pinX.std hH hH
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX j (le_of_lt hj)))
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX (j + 1) hj))
  classical
  refine ⟨fun t j => if h : j < B.R.m then (key t j h).choose else 1, fun t j hj => ?_⟩
  simp only [dif_pos hj]
  exact (key t j hj).choose_spec

end GlobalTheory.Fam.KomExist
