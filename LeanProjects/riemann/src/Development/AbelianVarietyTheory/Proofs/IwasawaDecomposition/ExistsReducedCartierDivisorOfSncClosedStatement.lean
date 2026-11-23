import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] (T : TopologicalSpace.Closeds X), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → j (genericPoint Y) ∉ T → ∃ D : CartierDiv Y, D.Eff ∧ (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧ ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g → ∀ (f : Y.functionField) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g) := by
  first | exact @GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | exact GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | (intros; apply GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv <;> assumption)
