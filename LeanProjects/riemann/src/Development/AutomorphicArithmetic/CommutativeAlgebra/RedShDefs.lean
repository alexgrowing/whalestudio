import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.RedSh

def Conn {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (m : ℤ) : Prop :=
  (∀ n, n < m → Function.Bijective (pull R f F n)) ∧ Function.Injective (pull R f F m)

def idemIdeal {B : Type} [CommRing B] (P : Ideal B) : Ideal B :=
  Ideal.span {e | IsIdempotentElem e ∧ e ∈ P}

def GoodRing (B : Type) [CommRing B] : Prop :=
  ∀ P : Ideal B, P.IsPrime →
    ∃ (_ : IsDomain (B ⧸ idemIdeal P)) (_ : IsLocalRing (B ⧸ idemIdeal P)), AIC (B ⧸ idemIdeal P)

def IntSH (q : ℕ) (R : Type) [CommRing R] : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : Algebra A R), SH A ∧ IsUnit (q : A) ∧ Algebra.IsIntegral A R

end UpperTheory.RedSh
