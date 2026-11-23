import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  first | exact @GlobalTheory.DetLine.exists_wedgeCoord | exact GlobalTheory.DetLine.exists_wedgeCoord | (intros; apply GlobalTheory.DetLine.exists_wedgeCoord <;> assumption)
