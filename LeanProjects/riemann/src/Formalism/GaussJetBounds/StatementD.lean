import Formalism.GaussJetBounds.Statement

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def BasisChange : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (J m N : ℕ)
    (lam : Fin J → Fin N → K) (y : Fin m → Fin N → K),
    (∀ i a, ‖lam i a‖ ≤ 1) → (∀ k a, ‖y k a‖ ≤ 1) →
    ∀ e : Fin J → Fin m, Function.Injective e →
    ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1 →
    ∃ T : Matrix (Fin m) (Fin m) K, (∀ k k', ‖T k k'‖ ≤ 1) ∧ ‖T.det‖ = 1 ∧
      ∀ i k, (∑ a, lam i a * ∑ k', T k k' * y k' a) = if k = e i then 1 else 0

def DegProd : Prop :=
  ∀ (R : Type u) [CommRing R] (σ κ : Type) [DecidableEq κ] (blk : σ → Option κ) (n : ℕ)
    (f : Fin n → MvPolynomial σ R) (bd : Fin n → ℕ),
    (∀ c, ∀ mono ∈ (f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ bd c) →
    ∀ mono ∈ (∏ c, f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ ∑ c, bd c

def MinorDegAll : Prop :=
  ∀ (R : Type u) [CommRing R] (m p : ℕ) (T : Fin p → Fin m → R),
    ∀ mono ∈ (Matrix.of fun (i c : Fin p) =>
        (∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (k, c) : MvPolynomial (Fin m × Fin p) R)).det.support,
      ∀ k : Fin m, (∑ c : Fin p, mono (k, c)) ≤ 1

def JCount : Prop :=
  ∀ l a : ℕ, 2 ≤ l → 1 ≤ a →
    (((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℝ) ≤
      2 * Real.logb l a + 1

end Formalism.DworkPowerSeriesWeights
