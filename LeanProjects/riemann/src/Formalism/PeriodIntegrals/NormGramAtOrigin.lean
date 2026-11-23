import Mathlib

noncomputable section

namespace PI.NormGramAtOrigin

section G

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j

end G

def gram {E : Type} [Field E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Fin r → Fin n → E) :
    Matrix (Fin r) (Fin r) E := fun a b => hform σ J (X a) (X b)

def Statement : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] [CharZero E] (n r : ℕ), r ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) E, (∀ i j, star (J j i) = J i j) → J.det ≠ 0 →
      ∃ X : Fin r → Fin n → E, (gram (starRingEnd E) J X).det ≠ 0

end PI.NormGramAtOrigin
