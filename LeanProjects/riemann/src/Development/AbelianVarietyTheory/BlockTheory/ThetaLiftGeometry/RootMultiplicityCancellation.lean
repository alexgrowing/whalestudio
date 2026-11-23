import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertiaTypeCancellation

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def pDelta (i : N.Loc) : ℕ := if N.l i = H.pde then H.pde' else H.pde

abbrev inertia (w : PlE H) : Subgroup (G H.E N.Om) := Ine (F := H.E) (N.plOm.1 w)

def chiC (i : N.Loc) (σ : G H.E N.Om) : ℂ :=
  iotaO N A i (chi1 N i σ)

def HasInertia (i : N.Loc) (w : PlE H) (L : A.LP w) (a b : ℕ) : Prop :=
  A.mono0 L ∧ ∀ σ ∈ inertia N w, A.inePol L σ = (X - 1) ^ a * (X - C (chiC N A i σ)) ^ b

def DeltaOrder : Prop :=
  ∀ (i : N.Loc) (w : PlE H), w ∈ placesOver H.E (pDelta N i) →
    orderOf ((N.chi i 1).comp (inertia N w).subtype) = 15

def TypeAtQDelta : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (w : PlE H), (w ∈ N.Q i ∨ w ∈ placesOver H.E (pDelta N i)) →
    HasInertia N A i w (A.locV i P w) R.r R.t

def TypeAtTypePrimes : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    ¬ (X - C (chiC N A i (N.gam0 i w))) ^ (R.t + 1) ∣ A.inePol (A.locV i P w) (N.gam0 i w) →
    ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim b = R.t ∧ HasInertia N A i w b 0 R.t

def Cancel : Prop :=
  ∀ (w : PlE H) (a b c : A.LP w), A.lpSum a b = A.lpSum a c → b = c

def InertialTypes : Prop :=
  DeltaOrder N ∧ TypeAtQDelta N A ∧ TypeAtTypePrimes N A ∧ Cancel N A

def TameAtTypePrimes : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    (∀ σ ∈ inertia N w, σ ∈ wildSet N (N.plOm.1 w) → A.inePol (A.locV i P w) σ = (X - 1) ^ R.nV) ∧
    (X - C (chiC N A i (N.gam0 i w))) ^ R.t ∣ A.inePol (A.locV i P w) (N.gam0 i w)

end GlobalTheory.IndefiniteRowSideFullHecke.InertiaTypeCancellation

end
