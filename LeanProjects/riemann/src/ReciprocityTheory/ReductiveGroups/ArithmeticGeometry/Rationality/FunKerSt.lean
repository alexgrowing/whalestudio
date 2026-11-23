import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

def FunKerStatement : Prop :=
  ∀ (K Ω V : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [AddCommGroup V]
    [Module K V] (U : Submodule K V) [FiniteDimensional K U]
    (Wc : Submodule Ω (Ω ⊗[K] V)) (FF : Set (Module.Dual Ω (Ω ⊗[K] V))),
    Wc ≤ baseSpan Ω U →
    (∀ c ∈ FF, ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, Wc ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan Ω U, x ∉ Wc → ∃ c ∈ FF, c x ≠ 0) →
    (∀ c ∈ FF, ∀ K₂ : IntermediateField K Ω, FiniteDimensional K K₂ → IsGalois K K₂ →
      DefinedOver c K₂ → ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc,
        c (inclT K₂ V (galAct σ x)) = 0) →
    ∃ W : Submodule K V, W ≤ U ∧ Submodule.span Ω ((fun v => (1 : Ω) ⊗ₜ[K] v) '' (W : Set V)) = Wc ∧
      ∃ K₁ : IntermediateField K Ω, FiniteDimensional K K₁ ∧
        ∃ (ρ : ℕ) (c : Fin ρ → Module.Dual Ω (Ω ⊗[K] V)),
          (∀ i, c i ∈ FF ∧ DefinedOver (c i) K₁) ∧
          (∀ x ∈ baseSpan K₁ U, (∀ i, c i (inclT K₁ V x) = 0) ↔ x ∈ baseSpan K₁ W) ∧
          Module.finrank K W + ρ = Module.finrank K U

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
