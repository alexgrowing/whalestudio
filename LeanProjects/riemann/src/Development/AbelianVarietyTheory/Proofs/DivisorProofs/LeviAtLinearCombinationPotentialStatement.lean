import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviAt_linear_combination_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ι : Type) [Fintype ι] (P : ι → LocPot X) (a : ι → ℝ) (u : X → ℝ), (∀ i, IsPotential A (P i)) → A.Smooth u → ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A (InhabCalc.combPot P a u) j y w = ∑ i, a i * leviAt A (P i) j y w + leviAt A (LocPot.ofFun u) j y w := by
  first | exact @GlobalTheory.Adopt.leviAt_linear_combination_potential | exact GlobalTheory.Adopt.leviAt_linear_combination_potential | (intros; apply GlobalTheory.Adopt.leviAt_linear_combination_potential <;> assumption)
