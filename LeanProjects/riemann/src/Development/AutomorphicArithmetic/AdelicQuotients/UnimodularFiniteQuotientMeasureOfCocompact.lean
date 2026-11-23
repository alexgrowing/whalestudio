import GroundTheory.AutomorphicForms.TraceFormulaWeil
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.unimodular_finite_quotientMeasure_of_cocompact :
    ∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Λ : Subgroup T) [DiscreteTopology Λ] (ν : Measure T) [ν.IsHaarMeasure],
        (∃ C : Set T, IsCompact C ∧ ∀ t : T, ∃ g ∈ Λ, ∃ y ∈ C, t = g * y) →
        ν.IsMulRightInvariant ∧ ν.IsInvInvariant ∧ quotientMeasure Λ ν Set.univ < ⊤ := by
  intro T _ _ _ _ _ _ _ _ Λ _ ν _ hC
  obtain ⟨C, hC, h⟩ := hC
  haveI : CompactSpace (RightCosetSpace Λ) := by
    refine ⟨(hC.image (RightCosetSpace.continuous_mk Λ)).of_isClosed_subset isClosed_univ ?_⟩
    intro x _
    obtain ⟨t, rfl⟩ := RightCosetSpace.mk_surjective Λ x
    obtain ⟨g, hg, y, hy, rfl⟩ := h t
    exact ⟨y, hy, (RightCosetSpace.mk_mul_of_mem hg y).symm⟩
  haveI hr : ν.IsMulRightInvariant := RightCosetSpace.isMulRightInvariant_of_compactSpace Λ ν
  haveI := RightCosetSpace.isFiniteMeasure (Γ := Λ) ν
  exact ⟨hr, ⟨RightCosetSpace.inv_eq_self_of_isMulRightInvariant ν⟩, measure_lt_top _ _⟩
