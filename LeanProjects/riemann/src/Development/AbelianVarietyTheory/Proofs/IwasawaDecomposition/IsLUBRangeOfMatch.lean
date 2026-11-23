import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad
open GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.ProjVar

namespace GlobalTheory.ShFam.DeKeyTrue

def kaKey : ℝ := -(1 / 2) * Real.log (2 * Real.pi)

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

theorem divOf_neg_exOf {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp) (la : GlobalTheory.AllWt.Weight S.Dw) :
    divOf (Φ.C k) (fun z => -GlobalTheory.AllWt.exOf S.Dw la 0 (some z)) = (Φ.C k).Lw la := by
  simp only [divOf, FlagCpt.Lw, FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_smul, Finset.sum_neg_distrib]

def hodgeLw {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ)
    (la : GlobalTheory.AllWt.Weight S.Dw) : (cxSt D.what₂.LL).Met (Φ.C k).Y σ ((Φ.C k).Lw la) :=
  divOf_neg_exOf Φ k la ▸ metsOf x Φ k none σ (fun z => -GlobalTheory.AllWt.exOf S.Dw la 0 (some z))

variable (s : FinalTheorems S κ)

def KeyNormedAt (key : KeySec s.Xo κ.c) : Prop :=
  ∀ (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (k : (s.U σ).Comp) (x : ((s.U σ).X k).dom),
    (∀ τ i, ‖ReciprocityTheory.ChartRestriction.G.FD.dmin ((s.U σ).X k).Gm x.1 τ i‖ = 1) →
    Formalism.L2.PjFree.lieFac S.Dw (xiR D) (fun _ => 1) *
      ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c (key.ρ : Rul s.Xo κ.c) ((s.U σ).un k x))‖ =
      Real.exp (-((D.R.f * D.R.r : ℕ) : ℝ) * kaKey)

def recVal (σ₀ : κ.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : Rul s.Xo κ.c)
    (p : Formalism.L2.PjFree.FPt (s.U σ₀).X) : ℝ :=
  Formalism.L2.PjFree.lieFac S.Dw (xiR D) a *
    ((s.U σ₀).X p.1).pnorm (Formalism.L2.PjFree.laU (s.U σ₀) a n p.1) (Formalism.L2.PjFree.rdU (s.U σ₀) g p.1) p.2

def flagVal (Φ : s.Flag) (x : ToroidalCompactificationData s) (key : KeySec s.Xo κ.c) (la : GlobalTheory.AllWt.Weight S.Dw) (n : ℕ)
    (g : Rul s.Xo κ.c) (σ : D.what₂.LL →+* ℂ) (q : Σ k : s.Comp, (geoTrue D.what₂.LL).pts (Φ.C k).Y σ) : ℝ :=
  Real.exp ((n : ℝ) / 2 * ((D.R.f * D.R.r : ℕ) : ℝ) * kaKey) *
    Real.sqrt ((geoTrue D.what₂.LL).pn (Φ.C q.1).Y σ ((Φ.C q.1).Lw la) (hodgeLw x Φ q.1 σ la)
      ((geoTrue D.what₂.LL).cx (Φ.C q.1).Y σ ((Φ.C q.1).val (g * (key.ρ : Rul s.Xo κ.c) ^ (n / 2)))) q.2)

end FinalTheorems

end GlobalTheory.ShFam.DeKeyTrue

namespace GlobalTheory.ShFam.DeKeyTrue

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end FinalTheorems

end GlobalTheory.ShFam.DeKeyTrue

namespace GlobalTheory.ShFam.DeKeyTrue

variable {D : D7} {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ}

def ruleAt (Φ : FamOver Q T h c) {j : ℕ} (hj : InR D j) (f : T.R j) :
    Rul (Φ.F.at (datW D Φ.F.κg j)).Xo (datW D Φ.F.κg j).κ.c :=
  trRul (Φ.t.same j hj) (c := T.Q.c) (c' := Φ.F.κg.c) Φ.t.le f

def hmOf (Φ : FamOver Q T h c) (j : ℕ) (x : ToroidalCompactificationData (Φ.F.at (datW D Φ.F.κg j))) :
    ∀ (k : (Φ.fam.U (datW D Φ.fam.κg j)).Comp) (σ : D.what₂.LL →+* ℂ)
      (lam : D.what₂.Tau → Fin (datW D Φ.fam.κg j).N → ℤ),
      (geoTrue D.what₂.LL).Met ((Φ.fam.U (datW D Φ.fam.κg j)).alg.Yv k) σ
        ((Φ.fam.U (datW D Φ.fam.κg j)).alg.Lw k lam) :=
  fun k σ lam => hodgeLw x (Φ.k.at (datW D Φ.F.κg j)).Φ k σ ((Φ.F.sig _ _ _ _).wt Φ.L lam)

def KeyNormed (Φ : FamOver Q T h c) (j : ℕ) : Prop :=
  KeyNormedAt (Φ.F.at (datW D Φ.F.κg j)) (Φ.k.at (datW D Φ.F.κg j)).key

end GlobalTheory.ShFam.DeKeyTrue
