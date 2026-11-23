import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts

set_option genSizeOfSpec false
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)

structure QLev {v : VCom f.c} {t : W.P.T} (F : GlobalTheory.QPl.QFam v (f.t t)) : Prop where
  places : ∃ pl : Fin F.r ≃ (pk W).Q t, ∀ i, Formalism.L2.NTheta.IsIdemAt (F.Q i).q.e (pl i).1 ∧ (F.Q i).q.v = (pl i).1.under (𝓞 D.host.F)
  mid : ∀ i j d hd, j < D.R.m → ∀ x ∈ KO (F.Q i).k _,
    ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j ∈ levS _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ ((F.Q i).T.lev j d hd).J) ∧
    ∀ hx : x ∈ ((F.Q i).T.lev j d hd).J, levChi _ ((pk W).βY j) ((pk W).datYt t j (lvP W))
      ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j) = (((F.Q i).T.lev j d hd).lam ⟨x, hx⟩ : ℂ)
  top : ∀ i, ∀ x ∈ KO (F.Q i).k _, ∀ g, (ofSplit (F.Q i).q).IsLoc (F.Q i).FT g x →
    (f.g.bT⁻¹ * g * f.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ (F.Q i).T.levTop.J)

def VfAt (v : VCom f.c) {t : W.P.T} (w : VTup (f.t t)) (sc : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (f.t t).om j (a * v.b j, a' * v.b (j + 1)) ((f.t t).pt j P) =
    sc j • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ (w.eQ j) (v.Ψ j P a a'))) ∧
  ∀ j h P, (f.t t).omT j h (v.b (j + 1), v.bT) ((f.t t).ptT j h P) =
    sc (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ (w.eQT j h) (v.ΨT j h P))

def GVec (v : VCom f.c) (s : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d → ∀ P, ∀ a ∈ GinfC _,
    ∀ a' ∈ GinfC _, (pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j)
      (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)) =
      s j • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a')) ∧
  ∀ j h d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → ∀ P,
    omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)) =
      s (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P)

end GlobalTheory.Fam

end
