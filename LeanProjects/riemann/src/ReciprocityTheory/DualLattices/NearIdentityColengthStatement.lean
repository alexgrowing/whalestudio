import Mathlib

namespace ReciprocityTheory.PGsh

open Matrix

def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G

def ColengthSumStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (e : G ≃ AddChar G K) (B₁ B₂ : Matrix G G K),
    (Matrix.of fun g h : G => e h g) = B₁ * B₂ᵀ →
    (v B₁.det * v B₂.det) ^ 2 = v (Fintype.card G : K) ^ Fintype.card G

def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)

def DigitCountStatement : Prop :=
  ∀ (R : Type) [CommRing R] (p h : ℕ) (e : Fin h → R),
    2 * ∑ α : Fin h → Fin p, ∑ j, ((α j : ℕ) : R) * e j =
      (p : R) ^ h * ((p : R) - 1) * ∑ j, e j

def LinearMonomialBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : ℕ) (k : Type) [Field k] [CharP k p]
    (A : Matrix (Fin h) (Fin h) k), IsUnit A.det →
    ∀ e : (Fin h → Fin p) ≃ (Fin h → ZMod p),
      (Matrix.of fun x y : Fin h → ZMod p =>
        ∏ j, (∑ i, A j i * ZMod.castHom (dvd_refl p) k (x i)) ^ ((e.symm y j : Fin p) : ℕ)).det ≠ 0

def NearIdentityColengthStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι K) (s : ι → K),
    (∀ i j, v (U i j) ≤ 1) → (∀ i j, v (U i j - (1 : Matrix ι ι K) i j) < 1) →
    v (U * Matrix.diagonal s).det = ∏ i, v (s i)

def ColengthZeroStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι K),
    (∀ i j, v (T i j) ≤ 1) → v T.det = 1 → ∀ i j, v (T⁻¹ i j) ≤ 1

end ReciprocityTheory.PGsh
