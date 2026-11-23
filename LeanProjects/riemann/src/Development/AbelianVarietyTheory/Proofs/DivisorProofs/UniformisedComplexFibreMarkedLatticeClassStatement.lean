import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, 0 < N → N.Coprime p → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∃ t', D.Cls N D' t' ∧ ∀ a, ∃ x, t' a = t a + N • x := by
  first | exact @GlobalTheory.UPel.HT.unifAt_cls | exact GlobalTheory.UPel.HT.unifAt_cls | (intros; apply GlobalTheory.UPel.HT.unifAt_cls <;> assumption)
