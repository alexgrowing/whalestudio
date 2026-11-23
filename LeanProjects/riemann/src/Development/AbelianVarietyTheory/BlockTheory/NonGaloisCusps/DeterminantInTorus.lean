import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section One

variable (D : D7) (i : D.nd.Loc)

def IsRxBar (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((r g : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
    Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i)))) ∧
  IsSSRep r ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      (heckePol D.nd i x w).map (iotaOQ D.nd D.naut i)

def CoeffLarge : Prop :=
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), IsRxBar D i x r →
    ∃ h : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ (g : GE D.nd) (a b : Fin D.R.nV),
      ((h * r g * h⁻¹ : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) a b ∈ (D.naut.iotaQ i).range

def IsRx (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i)) ∧
  IsSSRep (mapRep (toK D.nd i) r) ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpoly = heckePol D.nd i x w

def DetInT (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ g : GE D.nd, ∃ P : Polynomial (D.nd.T i), ∀ x : D.nd.X i,
    P.map (evT D.nd i x) = ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpolyRev

def RxConcl : Prop :=
  ∃ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), (∀ x, IsRx D i x (r x)) ∧ DetInT D i r

def DetInTAll : Prop :=
  ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), (∀ x, IsRx D i x (r x)) → DetInT D i r

end One

def RxBar_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ r, IsRxBar D i x r

def RxDetInT_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, CoeffLarge D i → RxConcl D i

def RxDetInTF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ p : Fm.Ix x, RxDetInT_at (Fm.D x p)

def RxDetInT (C : FamClass) : Prop :=
  Closed C (fun Fm _ => RxDetInTF Fm)

theorem isRx_iff (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) :
    (∀ x, IsRx D i x (r x)) ↔ GoodR D.nd i r := Iff.rfl

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

end
