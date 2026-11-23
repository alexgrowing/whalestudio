import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsClassifyMarkedPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_classify_markedPeriods : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  first | (exact @GlobalTheory.UPel.HT.Model.fineAt_univ) | (exact GlobalTheory.UPel.HT.Model.fineAt_univ) | (intros; apply GlobalTheory.UPel.HT.Model.fineAt_univ <;> assumption)
