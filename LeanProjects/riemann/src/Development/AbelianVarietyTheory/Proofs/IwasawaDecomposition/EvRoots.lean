import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section CapelliMinorMembership

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def piCoef (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : Formalism.IndefR.NX.U D.nd) : ↥D.LL0 :=
  (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * (((psiUOf D.nd (NX.xiRed D) θ u)⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

def eLop (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g

def piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, ((piCoef D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j (u : G0g D.nd)

open Classical in

def evRoots (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Finset ↥D.LL0 :=
  (Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ).image fun σ => In.eig j σ k P

def evPol (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Polynomial ↥D.LL0 :=
  ∏ r ∈ evRoots D S In j k P, (X - C r)

def phiLop (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End D.what₂.LL (S.WL j) :=
  aeval (In.hL j k P) ((evPol D S In j k P).map (algebraMap ↥D.LL0 D.what₂.LL))

def hLT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
    Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

def piKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap

def phiKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  aeval (hLT D T S In i j b k P) ((evPol D S In j k P).map (readT D T i b))

theorem hkT_eq (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkT D T S In i j b k P = (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k • hLT D T S In i j b k P :=
  rfl

end CapelliMinorMembership

end GlobalTheory.HeightCounting.FormsStep
