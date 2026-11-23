import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

abbrev FYFam {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) : Type :=
  ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)

def IsNormalFr {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (FY : FYFam l) (sc : ℕ → l.k) : Prop :=
  (∀ j, valuation l.k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi) ∧
  (∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1) ∧
  (∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega))
    (FY j c hc)) ∧
  (∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)) ∧
  ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)

end GlobalTheory.Fam

end
