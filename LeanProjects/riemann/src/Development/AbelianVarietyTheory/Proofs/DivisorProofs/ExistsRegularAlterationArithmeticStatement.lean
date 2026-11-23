import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularAlterationArithmetic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_alteration_arithmetic : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (ρ : Y' ⟶ Y), CxForm.IsRegVar (ρ ≫ q) e ∧ ρ (genericPoint Y') = genericPoint Y ∧ ρ.residueDegree (genericPoint Y') ≠ 0 := by
  first | exact @GlobalTheory.RegAlteration.exists_regular_alteration | exact GlobalTheory.RegAlteration.exists_regular_alteration | (intros; apply GlobalTheory.RegAlteration.exists_regular_alteration <;> assumption)
