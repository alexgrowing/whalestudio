import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ReducibleThreeDim
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas

noncomputable section

namespace Formalism.MainNotions.IdempotentChoiceDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Obj51

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

def IsOrthogonalIdempotentDecomposition (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
    N.l i - 1 ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    IsUnit (del51 N S S.π')) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

end Obj51

end Formalism.MainNotions.IdempotentChoiceDepthZero
