import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def ColumnWordEquivariance : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (n : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (Xr : ι → Fin n → R) (m : (Matrix (Fin n) (Fin n) R)ˣ) (l : ℕ),
    colWord primal isVec lt
        (fun i => if isVec i then Matrix.vecMul (Xr i) (↑m : Matrix _ _ R)
          else Matrix.vecMul (Xr i) (↑m⁻¹ : Matrix _ _ R).transpose) l =
      actF (colWord primal isVec lt Xr l)
        (if primal then (↑m : Matrix _ _ R) else (↑m⁻¹ : Matrix _ _ R).transpose)

def ColumnWordTruncation : Prop :=
  ∀ (R : Type) [CommRing R] (n N i : ℕ) (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (I : Finset (Fin n)), i ≤ N →
    ∃ Q : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R,
      (∀ I' , ∀ e ∈ (Q I').support, ∀ x ∈ e.support, i ≤ x.1) ∧
      pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) N I =
        ∑ I' : Finset (Fin n),
          pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) i I' * Q I'

def ValuationProductsComponents : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I → i ≤ N →
    (∀ m : Fin n, m.val + 1 = n →
      ((μ i m : ℤ) : WithTop ℤ) ≤
        valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl (psiPath k isVec μ N I))) ∧
    (∀ m : Fin n, m.val = 0 →
      lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl (psiPath k isVec μ N I)) ≤
        ((μ i m : ℤ) : WithBot ℤ))

def JacobiMinor : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (m : (Matrix (Fin n) (Fin n) R)ˣ) (I J : Finset (Fin n)),
    I.card = J.card →
    (↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J =
      (-1) ^ (∑ a ∈ I, a.val + ∑ b ∈ J, b.val) * minorF (↑m : Matrix (Fin n) (Fin n) R) Iᶜ Jᶜ

def IndexWeights : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)), Antitone μ → IsIndex μ I →
    ({c : ℤ | (I c).Nonempty}.Finite) ∧
    (∀ m m' : Fin n,
      μ m' ≤ ({c : ℤ | 1 ≤ c ∧ m ∈ I c}.ncard : ℤ) - ({c : ℤ | c ≤ 0 ∧ m ∈ I c}.ncard : ℤ) ∨ m'.val + 1 ≠ n) ∧
    (∀ m m' : Fin n,
      ({c : ℤ | 1 ≤ c ∧ m ∈ I c}.ncard : ℤ) - ({c : ℤ | c ≤ 0 ∧ m ∈ I c}.ncard : ℤ) ≤ μ m' ∨ m'.val ≠ 0) ∧
    (∀ m : Fin n,
      ({c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c}.ncard : ℤ) - ({c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c}.ncard : ℤ) = μ m)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
