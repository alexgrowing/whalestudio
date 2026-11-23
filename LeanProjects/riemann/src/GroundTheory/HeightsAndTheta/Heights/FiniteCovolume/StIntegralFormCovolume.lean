import Mathlib

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

def IntegralFormCovolume.Statement : Prop :=
  ∀ (ψ : Q →+ V) (e : Basis K ℚ Q) (T : LinearMap.BilinForm ℚ Q) (μ : Measure V),
    μ.IsAddHaarMeasure → T.Nondegenerate → LinearIndependent ℝ (fun k => ψ (e k)) →
    finrank ℝ V = Fintype.card K →
    ∃ C : ℝ, ∀ (L : AddSubgroup Q) (k : ℤ), k ≠ 0 → L.FG → Submodule.span ℚ (L : Set Q) = ⊤ →
      (∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, T x y = n) →
      (∀ y : Q, (∀ x ∈ L, ∃ n : ℤ, T y x = n) → k • y ∈ L) →
      ∃ _ : DiscreteTopology (AddSubgroup.toIntSubmodule (L.map ψ)),
        IsZLattice ℝ (AddSubgroup.toIntSubmodule (L.map ψ)) ∧
        ZLattice.covolume (AddSubgroup.toIntSubmodule (L.map ψ)) μ ^ 2 ≤
          C * |(k : ℝ)| ^ Fintype.card K

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
