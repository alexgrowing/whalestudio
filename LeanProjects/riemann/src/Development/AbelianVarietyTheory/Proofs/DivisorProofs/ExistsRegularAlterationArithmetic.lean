import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegAlteration

theorem exists_regular_alteration : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (ρ : Y' ⟶ Y), CxForm.IsRegVar (ρ ≫ q) e ∧ ρ (genericPoint Y') = genericPoint Y ∧ ρ.residueDegree (genericPoint Y') ≠ 0 := by
  intro H k _ Y _ q e h
  obtain ⟨Z, _, ρ, hZ, hr, hg, hd⟩ := H Y _ e (ShFam.Pad.isArithVar_toSpZ h)
  exact ⟨Z, inferInstance, ρ, ⟨RegCoverExists.isArithVar_of_toSpZ h.isDomain h.finite _ hZ, hr⟩, hg, hd⟩

end GlobalTheory.RegAlteration

end
