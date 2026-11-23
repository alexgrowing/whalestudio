import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleDimPlusOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_dim_plus_one : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules)
    (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2), IsProjOver p → GlobalTheory.VB.IsVB E₁ 2 →
    IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) → topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 := by
  first | exact @GlobalTheory.FlagLineDim.topologicalKrullDim_eq_add_one | exact GlobalTheory.FlagLineDim.topologicalKrullDim_eq_add_one | (intros; apply GlobalTheory.FlagLineDim.topologicalKrullDim_eq_add_one <;> assumption)
