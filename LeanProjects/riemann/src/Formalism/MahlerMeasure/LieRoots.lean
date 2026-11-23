import Formalism.MahlerMeasure.StatementD

namespace Formalism.GM

open Finset Polynomial

open Classical in
def LieMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (((binMatK K del₀ c).det).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤
      (p : ℝ) ^ (-(E * (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card))

def LieRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (h β : ℕ) (E : ℝ) (D : K[X]) (lead : K) (roots : Multiset K) (t₀ : ℤ),
    0 ≤ E → lead ≠ 0 →
    D = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (D.comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤ (p : ℝ) ^ (-(E * β)) →
    (β : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)

end Formalism.GM
