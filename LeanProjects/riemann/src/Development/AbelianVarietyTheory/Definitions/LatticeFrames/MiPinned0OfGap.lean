import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.ConcreteSettingExists

namespace GlobalTheory.Core.Rk

theorem finX_of_gap : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc⟩
  Formalism.L2.SG.Pf.finXC_of GlobalTheory.wuDecayOfGap CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

def STrue0.ofGap {D : D7} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue0 D F₀) (h : GapHyp D) : STrue D F₀ :=
  S.withFin (finX_of_gap D S.toSTies h)

def STrue.equivOfGap {D : D7} (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (h : GapHyp D) : STrue D F₀ ≃ STrue0 D F₀ where
  toFun S := S.bare
  invFun S := S.ofGap h
  left_inv _ := rfl
  right_inv _ := rfl

def STrue0.ofSTiesR {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {R : Formalism.L2.RecT ex} (S : STiesR R)
    (pin : ∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) : STrue0 D fun u => (R.T.cols.forms u).to0 where
  toSTies := S.toSTies
  tr := S.tr
  into := S.into
  bij := S.bij
  lev := S.lev
  colPin := S.colPin
  inst := S.inst
  locTied := S.locTied
  pin := pin

section Worlds

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def World0.ofGap (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : World I l Z := w.withFin (finX_of_gap _ w.S.toSTies h)

theorem World0.ofGap_C (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).C = w.C := rfl

theorem World0.ofGap_toSTies (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).S.toSTies = w.S.toSTies := rfl

theorem World0.bare_ofGap (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).bare = w := rfl

theorem World0.of_forall_world {Q : World0 I l Z → Prop} (hQ : ∀ w : World I l Z, Q w.bare) (h : GapHyp (I.rec7 l Z))
    (w : World0 I l Z) : Q w := hQ (w.ofGap h)

theorem miPinned0_of_gap {u : (I.rec7 l Z).what₂.Word} (hQ : ∀ w : World I l Z, MIPinned w u) (h : GapHyp (I.rec7 l Z))
    (w : World0 I l Z) : MIPinned0 w u := (miPinned_withFin_iff w _ u).1 (hQ (w.ofGap h))

end Worlds

theorem trueD_iff_of_gap {D : D7} (h : GapHyp D) : TrueD D ↔ IsTrueColumnDatum D := trueD_iff fun T => finX_of_gap D T h

theorem IsTrueColumnDatum.of_forall_trueD {Q : D7 → Prop} (hQ : ∀ D, TrueD D → Q D) {D : D7} (hD : IsTrueColumnDatum D) (h : GapHyp D) : Q D :=
  hQ D ((trueD_iff_of_gap h).2 hD)

end GlobalTheory.Core.Rk

end
