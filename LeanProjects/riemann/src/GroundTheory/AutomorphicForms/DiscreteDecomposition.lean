import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory

namespace GroundTheory.Automorphic

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isCompactOperator_integrated (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  isCompactOperator_integrated_rightRegularRep Γ μ f

theorem exists_isHilbertSum_isIrreducible_finite :
    ∃ s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))),
      ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))),
      ∃ hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V,
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
        (fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ) ∧
      (∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible) ∧
      ∀ {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (σ : UnitaryRep G K), σ.IsIrreducible →
          {V : s | ((rightRegularRep Γ μ).restrict V (hinv V)).IsEquivalent σ}.Finite := by
  have hcpt := isCompactOperator_integrated Γ μ
  obtain ⟨s, hcomp, hinv, hsum, hirr⟩ := UnitaryRep.exists_isHilbertSum_isIrreducible hcpt
  exact ⟨s, hcomp, hinv, hsum, hirr, fun σ hσ =>
    UnitaryRep.finite_setOf_isEquivalent hcpt hinv hsum.OrthogonalFamily hσ⟩

theorem finiteDimensional_intertwiners {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    FiniteDimensional ℂ (σ.intertwiners (rightRegularRep Γ μ)) :=
  UnitaryRep.finiteDimensional_intertwiners (isCompactOperator_integrated Γ μ) hσ

end RightCosetSpace

end GroundTheory.Automorphic
