import Mathlib

open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.FN

def succMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) (K : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}

def succMinBall {r : ℕ} (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧
    i ≤ Module.finrank ℝ (Submodule.span ℝ ((R : Set (EuclideanSpace ℝ (Fin r))) ∩ Metric.closedBall 0 t))}

def MinkowskiIIUpper : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
        ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ

def MinkowskiIILower : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      (2 : ℝ) ^ finrank ℝ E / (Nat.factorial (finrank ℝ E) : ℝ) * ZLattice.covolume L μ
        ≤ μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)

def MinkowskiIIBall : Prop :=
  ∀ (r : ℕ) (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology R] [IsZLattice ℝ R],
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal *
        ∏ i : Fin r, succMinBall R ((i : ℕ) + 1)
      ≤ 2 ^ r * ZLattice.covolume R

end Formalism.FN
