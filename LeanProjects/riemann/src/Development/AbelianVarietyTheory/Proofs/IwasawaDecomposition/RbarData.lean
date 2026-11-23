import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

def ssRep {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k :=
  Classical.epsilon fun ρ' : Γ →* GL (Fin a) k => IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
    ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly

def BcGood (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧ ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = Rw.locR σ w

open Classical in

def bcOf (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, BcGood D Rw σ Sig then Multiset.ofList (h.choose.map fun p => (p.a, p.d)) else {(D.R.r, 1)}

def RbarData {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) : Prop :=
  ∃ i : X.nd.Loc, X.nd.w i = lam ∧ ∃ (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)),
    HasParamW X.nd Y.naut i σ Sig ∧ IsRepOfSig X.nd Y.naut i Sig ρ

open Classical in

def rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    G D.host.E X.nd.Om →* GL (Fin D.R.r) (Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam)) :=
  if h : RbarData Y σ lam then
    ssRep (mapRep (((fbCast (h.choose_spec.1 ▸ X.nd.w_l h.choose).symm (X.nd.lPrime h.choose).out
        (D.what₂.places.resChar_prime lam)).toRingHom.comp
      ((Y.naut.kFbar h.choose).comp (IsLocalRing.residue (X.nd.O h.choose))))) h.choose_spec.2.choose_spec.choose)
  else 1

def mtSup {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (i : X.nd.Loc) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i)) :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧
      IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P

def castMt {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j)) :
    Submodule ℂ (D.what₂.Mt μ' j') := by
  subst h1; subst h2; exact M

open Classical in

def mtParOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (μ : D.what₂.Tup) (j : ℕ) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  if h : ∃ i, X.nd.mu i = μ ∧ X.nd.j i = j then castMt h.choose_spec.1 h.choose_spec.2 (mtSup Y h.choose σ') else ⊥

end GlobalTheory.HeightCounting

end
