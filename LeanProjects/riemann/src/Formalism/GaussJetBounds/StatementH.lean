import Mathlib

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def oldRowTop {R : Type u} [CommRing R] {N0 N1 m : ℕ} (T : Fin N0 → Fin m → R) (i : Fin N0)
    (b : Fin N1) : MvPolynomial (Option (Fin m) × Fin N1) R :=
  if i.val = 0 then MvPolynomial.X (none, b)
  else ∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (some k, b)

def oldRowLow {R : Type u} [CommRing R] {N0 N1 m : ℕ} (T : Fin N0 → Fin m → R) (i : Fin N0)
    (b : Fin N1) : MvPolynomial (Fin m × Fin N1) R :=
  ∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (k, b)

def minorProd {R : Type u} [CommRing R] {σ : Type} {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) : MvPolynomial σ R :=
  ∏ c, (Matrix.of fun (r r' : Fin (p c)) => row ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c r')).det

def MonoShapeTop : Prop :=
  ∀ (R : Type u) [CommRing R] (N0 N1 m C : ℕ) (T : Fin N0 → Fin m → R) (p : Fin C → ℕ)
    (hp : ∀ c, p c ≤ N0), (∀ c, 1 ≤ p c) → ∀ (I : ∀ c, Fin (p c) → Fin N1),
    ∀ mono ∈ (minorProd (oldRowTop (N1 := N1) T) p hp I).support,
      (∑ b : Fin N1, mono (none, b)) = C ∧
      (∑ k : Fin m, ∑ b : Fin N1, mono (some k, b)) = ∑ c, (p c - 1) ∧
      ∀ k : Fin m, (∑ b : Fin N1, mono (some k, b)) ≤ (Finset.univ.filter (fun c => 2 ≤ p c)).card

def MonoShapeLow : Prop :=
  ∀ (R : Type u) [CommRing R] (N0 N1 m C : ℕ) (T : Fin N0 → Fin m → R) (p : Fin C → ℕ)
    (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1),
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) T) p hp I).support,
      (∑ k : Fin m, ∑ b : Fin N1, mono (k, b)) = ∑ c, p c ∧
      ∀ k : Fin m, (∑ b : Fin N1, mono (k, b)) ≤ C

end Formalism.DworkPowerSeriesWeights
