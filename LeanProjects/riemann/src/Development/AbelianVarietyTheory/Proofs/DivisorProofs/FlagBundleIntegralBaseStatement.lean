import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleIntegralBase
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_integral_base : ∀ (Y Y₁ : Scheme.{0}) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    IsIntegral Y → GlobalTheory.VB.IsVB E₁ 2 → IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) → IsIntegral Y₁ := by
  first | exact @GlobalTheory.FlagBase.isIntegral_base | exact GlobalTheory.FlagBase.isIntegral_base | (intros; apply GlobalTheory.FlagBase.isIntegral_base <;> assumption)
