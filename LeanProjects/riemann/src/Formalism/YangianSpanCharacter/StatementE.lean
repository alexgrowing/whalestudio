import Mathlib

namespace Formalism.YangianSpanCharacter.E

def GGRatio : Prop :=
  ∀ (g : ℝ), 1 < g → ∀ k : ℕ,
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) =
      ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹

def GGProd : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ k : ℕ, ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹ ≤ 1 + 3 / g

def GGBound : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ (k : ℕ) (dimπ : ℝ), ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) ≤ dimπ →
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / dimπ ≤ 1 + 3 / g

def SpanChar : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (O : Subring K) (θ : K),
    θ ∈ O → θ ≠ 0 → ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent K (Sum.elim f f') →
    ∀ α α' : Fin n → K,
      (θ⁻¹ • (∑ i, α i • f i + ∑ i, α' i • f' i) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => θ⁻¹ • (f' i - f i))) ↔
        ∀ i, α' i ∈ O ∧ ∃ x ∈ O, α i + α' i = θ * x)

end Formalism.YangianSpanCharacter.E
