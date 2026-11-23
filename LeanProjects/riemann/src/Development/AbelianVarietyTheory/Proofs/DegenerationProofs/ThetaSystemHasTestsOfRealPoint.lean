import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExistStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVecStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEqStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTestMatch
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem hasTests_of_real : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hS hU hL hL2 hT o Ω _ _ _ _ S ρ
  have key : ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)),
      (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) →
      ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧
        ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
    intro p _ y₀ Fs hy
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_uniformised_model' hS hU hL.polBaseChange o Ω S ρ p y₀ Fs
    obtain ⟨l⟩ := GlobalTheory.T.uniformisedModel_torsionLabels_exist hL hL2 hT o Ω S ρ p y₀ u hy
    obtain ⟨τ, hτ⟩ := exists_test_match o Ω S ρ p y₀ u l
      (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o Ω S ρ p y₀ u l hy)
    exact ⟨u, l, τ, hτ, hu⟩
  refine ⟨?_, key⟩
  intro p _ y hy
  obtain ⟨_, _, τ, _⟩ := key p y ∅ hy
  exact ⟨τ⟩

end GlobalTheory.ZH
