import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

structure WDTie where

  e : ∀ w : PlE H, A.LP w ≃ WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)
  dim : ∀ w (a : A.LP w), (e w a).lpDim = A.lpDim a
  zero : ∀ w, e w (A.lpZero w) = WD.lpZero _
  sum : ∀ w (a b : A.LP w), e w (A.lpSum a b) = (e w a).lpSum (e w b)
  tw : ∀ w (a : A.LP w) (s : ℝ), e w (A.lpTw a s) = (e w a).lpTw s
  char : ∀ w (a χ : A.LP w), A.lpDim χ = 1 → e w (A.lpChar a χ) = (e w a).lpChar (e w χ)
  mono0 : ∀ w (a : A.LP w), A.mono0 a ↔ (e w a).mono0
  unr : ∀ w (a : A.LP w), A.unr a ↔ (e w a).unr
  frobEig : ∀ w (a : A.LP w), A.unr a → A.frobEig a = (e w a).frobEig
  tempered : ∀ w (a : A.LP w), A.tempered a ↔ (e w a).tempered
  inePol : ∀ w (a : A.LP w), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol a σ = (e w a).inePol σ

def WDTie.eig {N : NData R H what₂} {A : NAut N} (T : WDTie N A) (w : PlE H) (a : A.LP w) (σ : G H.E N.Om) :
    Multiset ℂ := ((T.e w a).inePol σ).roots

def CharLaws : Prop := ∀ (w : PlE H) (a b χ χ' : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpDim χ' = 1 →
  A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
  A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar a (A.lpTw χ s) = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar (A.lpChar a χ) χ' = A.lpChar a (A.lpChar χ χ') ∧
  A.lpChar a (A.lpUnr w {1}) = a

def Cancel : Prop := ∀ (w : PlE H) (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def LabTame : Prop := ∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)),
  (A.items₂ k (A.plGw k v) a).natDegree = A.lpDim a →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), σ ∈ wildSet N (N.plOm.1 (A.plGw k v)) →
    A.inePol a σ = (X - 1) ^ A.lpDim a

def PairLift (i : N.Loc) : Prop := ∀ σ P, Pairs N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)

def BCEx (i : N.Loc) : Prop := ∀ P : A.AV i, ∃ Pa, IsBCV N A i P Pa

def GalIso (i : N.Loc) : Prop := ∀ (P : A.AV i) (Pa : List (Part A.CG)), IsBCV N A i P Pa →
  ∃ r : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i)),
    Continuous (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
    IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      A.wdOf i r w = A.lpTw (isoLoc N A Pa w) ((1 - (R.nV : ℝ)) / 2)

def ChebSplit : Prop := ∀ S : Finset (PlE H), Dense {σ : G H.E N.Om | ∃ w : PlE H, w ∉ S ∧ IsSplitPl H w ∧
  ∃ B : ValuationSubring N.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ}

def SplitBC (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  ∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa'

def RepOfLoc (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  (∀ w, ¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w)) → P = P'

def twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) : A.LP w :=
  L.foldr (fun p acc => A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) acc) (A.lpZero w)

def IsobaricRigid : Prop := ∀ L L' : List ((Σ a : ℕ, A.CG a) × ℝ), (∀ p ∈ L, 1 ≤ p.1.1) → (∀ p ∈ L', 1 ≤ p.1.1) →
  (∀ᶠ w in Filter.cofinite, twSum N A L w = twSum N A L' w) → L.Perm L'

def RankOneUnitary {N : NData R H what₂} {A : NAut N} (T : WDTie N A) : Prop :=
  ∀ (π : A.CG 1) (w : PlE H) (σ : G H.E N.Om), IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ →
    ∀ α ∈ T.eig w (A.locG π w) σ, ‖α‖ = 1

def IotaRed (D : D7) : Prop := ∀ i : D.nd.Loc,
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
    (∀ y : D.nd.O i, ∃ h : iotaO D.nd D.naut i y ∈ B,
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
    ∀ k v x, ∃ h : D.ntypes.teichC k x ∈ B, D.ntypes.iota k v (D.nd.w i) x = κ (IsLocalRing.residue B ⟨_, h⟩)

def RowRepAtG (D : D7) : Prop := ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
  ∃ (Sig : List (Part D.naut.CG)) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
    HasParamW D.nd D.naut i σ Sig ∧ IsRepOfSig D.nd D.naut i Sig ρ ∧
    ∀ k v, D.nd.l i ≠ D.host.g k →
      D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v) =
        D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)

end GlobalTheory.RowTie
