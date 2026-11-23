import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

def qPrime (W : RealPack ex) (t : W.P.T) (p : ℕ) : Prop := ∃ PP ∈ (pk W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal

def RatioQ {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧ UnitRatio (qPrime W t) ((f.t t).cTop n / (f.t t).cBot)
    ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)

def ServedQ (W : RealPack ex) : Prop :=
  ∀ w (p : ℕ), p.Prime → qPrime W (W.Q.Rl.mu w) p → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal

def FamAllQ (W : RealPack ex) : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : FamCh W u) (d : BotDat W u),
    d.Pin z ∧ LawsX f.t ∧ LinkZero f d ∧ LinkTail f ∧ LinkDown f ∧ LinkOnto f ∧ LinkComm f ∧ RatioQ f

end GlobalTheory.MiTop

end
