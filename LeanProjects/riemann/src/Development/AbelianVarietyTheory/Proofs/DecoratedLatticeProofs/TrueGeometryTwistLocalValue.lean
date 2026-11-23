import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

theorem main : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ s j α γ hj
  refine ⟨?_, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atG j).2.1, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atT j).1⟩
  unfold QJ.dQ
  refine isFinComb_smul _ _ (isFinComb_smul _ _ (GlobalTheory.QPl.ThetaPin.isFinComb_aconv _ fun e he => ?_))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨ε, hε, hsum⟩ := (J.G i).q.above
  have hs := (J.G i).hs
  refine GlobalTheory.QPl.ThetaPin.isFinComb_of_half hε _ fun w hw => hsum ▸ ?_
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  rcases Nat.lt_or_ge j (J.G i).s with h1 | h1
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = (J.G i).s := ⟨(J.G i).s - j - 1, by omega⟩
    exact ((J.E i).dL_mid j d hd (α i) (γ i)).1 w hw
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      exact ((J.E i).dL_pen (α i) (γ i)).1 w hw
    · obtain rfl : j = (J.G i).s + 1 := by omega
      exact ((J.E i).dL_top (α i) (γ i)).1 w hw

end GlobalTheory.Fam.FinData
