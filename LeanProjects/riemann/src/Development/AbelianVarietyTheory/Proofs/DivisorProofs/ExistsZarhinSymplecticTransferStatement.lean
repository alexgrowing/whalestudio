import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinSymplecticTransfer : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  first | (exact @GlobalTheory.ZarhinFam.exists_kappaOK) | (exact GlobalTheory.ZarhinFam.exists_kappaOK) | (intros; apply GlobalTheory.ZarhinFam.exists_kappaOK  <;> assumption)
