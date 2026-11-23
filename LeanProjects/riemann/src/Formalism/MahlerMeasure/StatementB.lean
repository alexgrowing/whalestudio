import Formalism.MahlerMeasure.Statement

namespace Formalism.GM

open Finset Polynomial

noncomputable def binPoly (F : Type) [Field F] (t₀ : F) (i : ℕ) : F[X] :=
  Polynomial.C ((i.factorial : F)⁻¹) * (descPochhammer F i).comp (X - Polynomial.C t₀)

def MahlerDisc : Prop :=
  ∀ (p k i : ℕ) (t₀ : ℤ), p.Prime → i ≤ p ^ k →
    ∀ n : ℕ, padicNorm p
      ((Polynomial.C ((i.factorial : ℚ)⁻¹) *
        (descPochhammer ℚ i).comp (Polynomial.C ((p : ℚ) ^ k) * X + Polynomial.C (t₀ : ℚ))).coeff n) ≤ 1

def RowsDet : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)),
    (∀ i ∈ S, ∀ j, M i j ∈ I) → M.det ∈ I ^ S.card

def NewtonSpan : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (S : Subring F) (d : ℕ) (t₀ : ℤ) (P : F[X]),
    P.natDegree ≤ d → (∀ k : ℕ, k ≤ d → P.eval ((t₀ : F) + k) ∈ S) →
    ∃ c : Fin (d + 1) → F, (∀ i, c i ∈ S) ∧ P = ∑ i, Polynomial.C (c i) * binPoly F (t₀ : F) i

end Formalism.GM
