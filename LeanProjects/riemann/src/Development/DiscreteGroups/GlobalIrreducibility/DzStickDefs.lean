import Mathlib

noncomputable section

namespace DiscreteGroups.sglob.Stick

open NumberField IsDedekindDomain nonZeroDivisors

universe u

def dsum (p a : ℕ) : ℕ := (Nat.digits p a).sum

def psi (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra (ZMod p) k] {A : Type*} [CommRing A]
    (ζ : A) (hζ : ζ ^ p = 1) : AddChar k A :=
  (AddChar.zmodChar p hζ).compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom

structure GSDatum (p f : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (A : Type*) [CommRing A] [IsDedekindDomain A] (Q : HeightOneSpectrum A) where
  card_eq : Fintype.card k = p ^ f
  ι : k →+* A ⧸ Q.asIdeal
  ω : MulChar k A
  mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x
  ζ : A
  prim : IsPrimitiveRoot ζ p

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}

def ψ (D : GSDatum p f k A Q) : AddChar k A := psi p k D.ζ D.prim.pow_eq_one

def g (D : GSDatum p f k A Q) (a : ℕ) : A := gaussSum (D.ω ^ a)⁻¹ D.ψ

end GSDatum
end DiscreteGroups.sglob.Stick
