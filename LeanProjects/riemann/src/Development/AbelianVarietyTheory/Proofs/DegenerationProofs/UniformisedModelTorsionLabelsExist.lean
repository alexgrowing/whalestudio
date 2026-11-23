import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeightsStatement
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

theorem labels_exist : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → Nonempty u.Lab := by
  intro h₁ h₂ h₃ o Ω _ _ _ _ S ρ p _ y₀ u hy
  obtain ⟨q, hq, hq'⟩ := GlobalTheory.ZH.PsiForm.main o Ω S ρ p y₀ u
  obtain ⟨yy, hs, he⟩ := GlobalTheory.T.exists_labelMap_torsion_characters h₁ h₂ h₃ o Ω S ρ p y₀ u
  have hk := GlobalTheory.T.label_map_kernel_eq_integral_torsion h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he hy
  obtain ⟨hi, wt, hw⟩ := GlobalTheory.T.isoFree_perp_labelKernel_weights h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he
  exact ⟨⟨q, hq, hq', yy, hs, he, hk, hi, wt, hw⟩⟩

end GlobalTheory.ZH
