import Mathlib

open AlgebraicGeometry CategoryTheory

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

def IsMonomialIn (E : List X.IdealSheafData) (M : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι = ∏ i : Fin E.length, (E.get i).comap U.ι ^ a i

structure IsMonomialSplitting (E : List X.IdealSheafData) (I M N : X.IdealSheafData) :
    Prop where
  eq_mul : I = M * N
  monomial_support : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)
  monomial : IsMonomialIn E M
  transversal : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
    (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
    ¬ C ⊆ (N.support : Set X)

end FunctorialResolution.EmbeddedResolution
