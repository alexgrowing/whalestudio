import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightDictionaryLifting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Param

variable {R : Ranks} (P : HCParam R) (j : Fin R.m)

def run : Multiset ℚ :=
  (Finset.Icc 1 R.t).val.map fun c : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - (c : ℚ)

def param : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

end Param

variable (D : D7)

def liftIx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOf (ρ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def Induces (φ : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : Prop :=
  ∀ x : D.host.E, x ∈ D.host.F → φ x = embOf D ρ x

def typeU (ep : Bool) : Set (D.host.E →+* ℂ) :=
  {φ | (if ep then (starRingEnd ℂ).comp φ else φ) ∈
    D.host.cmType}

open Classical in

def sgn (ep : Bool) (φ : D.host.E →+* ℂ) : ℚ := if φ ∈ typeU D ep then 1 else -1

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev LocEmb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cxEmb (τ : LocEmb D i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    (((D.nbr i w hw).LL.1.val : Br.LL D.nbr i w hw →+* Qbar (D.nd.l i)).comp
      ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw)))

def JumpsAre {a : ℕ} (r : GE D.nd →* GL (Fin a) (D.nd.O i)) (τ : LocEmb D i w hw) (M : Multiset ℚ) : Prop :=
  (∀ p ∈ M, ∃ z : ℤ, p = z) ∧
    ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z = (M.count (z : ℚ) : ℤ)

end Local

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (D.nd.chi i c)

def IsSummand (i : D.nd.Loc) {a : ℕ} (r : GE D.nd →* GL (Fin a) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) :
    Prop :=
  ∃ (v : Fin a → KK D.nd i) (f : (Fin a → KK D.nd i) →ₗ[KK D.nd i] KK D.nd i), f v = 1 ∧
    (∀ g, (((r g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)).map (toK D.nd i)).mulVec v =
      toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v) ∧
    ∀ g u, f ((((r g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)).map (toK D.nd i)).mulVec u) =
      toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) * f u

def WeightTie : Prop := ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
  D.naut.infWt i (embOf D ρ) = (param (D.hc ρ) (liftIx D i)).map (fun p : ℚ => (p : ℂ) - 1 / 2) ∧
  D.naut.infWt i ((starRingEnd ℂ).comp (embOf D ρ)) =
    (param (D.hc ρ) (liftIx D i)).map (fun p : ℚ => -((p : ℂ) - 1 / 2))

def CharTie : Prop := ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
  D.naut.infG (D.naut.muC i) (embOf D ρ) = {-(((D.hc ρ).e (liftIx D i) : ℚ) : ℂ)} ∧
  D.naut.infG (D.naut.muC i) ((starRingEnd ℂ).comp (embOf D ρ)) = {(((D.hc ρ).e (liftIx D i) : ℚ) : ℂ)} ∧
  D.naut.infG D.naut.etaTinv (embOf D ρ) = {-(1 / 2 : ℂ)} ∧
  D.naut.infG D.naut.etaTinv ((starRingEnd ℂ).comp (embOf D ρ)) = {(1 / 2 : ℂ)}

abbrev Shift : Type := ℕ → D.what₂.places.Pl → (D.host.E →+* ℂ) → ℤ

def toJump (ep : Bool) (c : Shift D) (i : D.nd.Loc) (φ : D.host.E →+* ℂ) (p : ℚ) : ℚ :=
  sgn D ep φ * p + (c (D.nd.j i) (D.nd.w i) φ : ℚ)

def PointJumps (ep : Bool) (c : Shift D) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Br.IsdRW D.loc D.nbr i w hw r ∧
      ∀ (τ : LocEmb D i w hw) (ρ : D.what₂.Tau), Induces D (cxEmb D i w hw τ) ρ →
        JumpsAre D i w hw r τ
          ((param (D.hc ρ) (liftIx D i)).map (toJump D ep c i (cxEmb D i w hw τ)))

def PointCrys : Prop :=
  ∀ (i : D.nd.Loc), D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        Br.IsCrysW D.loc D.nbr i w hw r

def BlockSummand : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, ∀ (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i π r → ∀ k, 1 ≤ k → k ≤ D.R.t → IsSummand D i r (D.nd.chi i k)

def BlockJumps (ep : Bool) (c : Shift D) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : LocEmb D i w hw) (ρ : D.what₂.Tau), Induces D (cxEmb D i w hw τ) ρ →
    ∃ a : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ D.R.t → JumpsAre D i w hw (chiGL D i k) τ {(a : ℚ) + ((k : ℚ) - 1)}) ∧
      (run (D.hc ρ) (liftIx D i)).map (toJump D ep c i (cxEmb D i w hw τ)) =
        (Multiset.range D.R.t).map fun k : ℕ => (a : ℚ) + (k : ℚ)

def DictConcl : Prop :=
  (∃ (ep : Bool) (c : Shift D), PointJumps D ep c ∧ BlockJumps D ep c) ∧ PointCrys D ∧ BlockSummand D

def Dict_at : Prop := WeightTie D → CharTie D → DictConcl D

def DictF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Dict_at (Fm.D x i)

def DictClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => DictF Fm

example (φ : D.host.E →+* ℂ) : φ ∈ typeU D true ↔ (starRingEnd ℂ).comp φ ∈ typeU D false := Iff.rfl

example (ρ : D.what₂.Tau) : Induces D (embOf D ρ) ρ := fun _ _ => rfl

end GlobalTheory.IndefiniteRowSideFullHecke.WeightDictionaryLifting

end
