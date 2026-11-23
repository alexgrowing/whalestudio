import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsProportionalSeriesMatchTorsio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystems_proportional_series_match_torsion : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), n.Prime → Odd n → (∀ (k : ℕ) (x : La), 0 < k → k • x = 0 → x = 0) → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) → (∀ k m, 0 < k → 0 < m → ζ' (k * m) ^ m = ζ' k) → (∀ j, ζ' (n ^ j) = ζ (n ^ j)) → ∀ c₀ : C, c₀ ≠ 0 → (∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x)) → ∃ mt : GlobalTheory.Ex.Match N N' n, ∀ j p p', mt.r (n ^ j) p p' ↔ ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p' := by
  first | exact @GlobalTheory.ModelData.LabelMatch.exists_match | exact GlobalTheory.ModelData.LabelMatch.exists_match | (intros; apply GlobalTheory.ModelData.LabelMatch.exists_match <;> assumption)
