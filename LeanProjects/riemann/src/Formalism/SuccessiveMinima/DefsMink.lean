import Formalism.SuccessiveMinima.StatementMink

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

def latJ (n j : ℕ) : Set (Fin n → ℝ) :=
  {k | (∀ i, ∃ m : ℤ, k i = m) ∧ ∀ i : Fin n, j ≤ (i : ℕ) → k i = 0}

def boxJ (n j : ℕ) : Set (Fin n → ℝ) :=
  {u | ∀ i : Fin n, (i : ℕ) < j → 0 ≤ u i ∧ u i < 1}

def Gj (n j : ℕ) (A : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  volume (boxJ n j ∩ (A + latJ n j))

def GjTop : Prop := ∀ (n : ℕ) (A : Set (Fin n → ℝ)), Gj n n A ≤ 1

def GjLevel : Prop :=
  ∀ (n j : ℕ) (A : Set (Fin n → ℝ)), j < n → IsOpen A →
    (∀ x ∈ A, ∀ y ∈ A, (∀ i, ∃ m : ℤ, x i - y i = m) → ∀ i : Fin n, j ≤ (i : ℕ) → x i = y i) →
      Gj n j A ≤ Gj n (j + 1) A

def GjScale : Prop :=
  ∀ (n j : ℕ) (C : Set (Fin n → ℝ)) (t t' : ℝ), j ≤ n → IsOpen C → Convex ℝ C →
    (∀ x ∈ C, -x ∈ C) → Bornology.IsBounded C → 0 < t → t ≤ t' →
      ENNReal.ofReal ((t' / t) ^ (n - j)) * Gj n j (t • C) ≤ Gj n j (t' • C)

def MinkCore : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℝ)) (lam : Fin n → ℝ),
    IsOpen C → Convex ℝ C → (∀ x ∈ C, -x ∈ C) → Bornology.IsBounded C →
    (∀ i, 0 < lam i) → Monotone lam →
    (∀ j : Fin n, ∀ x ∈ lam j • C, ∀ y ∈ lam j • C, (∀ i, ∃ m : ℤ, x i - y i = m) →
        ∀ i : Fin n, j ≤ i → x i = y i) →
      (volume C).toReal * ∏ i, lam i ≤ 1

def SuccMinFacts : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
    ∃ v : Fin (finrank ℝ E) → E, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L) ∧
      (∀ i : Fin (finrank ℝ E), v i ∈ succMin L K ((i : ℕ) + 1) • K) ∧
      (∀ i : Fin (finrank ℝ E), 0 < succMin L K ((i : ℕ) + 1)) ∧
      Monotone (fun i : Fin (finrank ℝ E) => succMin L K ((i : ℕ) + 1)) ∧
      ∀ (i : Fin (finrank ℝ E)) (u : E), u ∈ L → u ∈ succMin L K ((i : ℕ) + 1) • interior K →
        u ∈ Submodule.span ℝ (v '' {k | k < i})

def AdaptedBasis : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ L) →
      ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, ∀ j : Fin (finrank ℝ E),
        Submodule.span ℝ ((fun i => (b i : E)) '' {k | k ≤ j}) =
          Submodule.span ℝ (v '' {k | k ≤ j})

end Formalism.FN
