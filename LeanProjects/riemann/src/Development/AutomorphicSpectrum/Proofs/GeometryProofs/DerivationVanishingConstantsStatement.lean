import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_vanishing_constants : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom → ∀ (V : G.left.Opens), IsAffineOpen V → ⊤ ≤ (1 : Over.mk (spMap φ) ⟶ G).left ⁻¹ᵁ V →
  ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V r) = 0) →
    (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f * D f' + valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f' * D f) →
    ∃! c : Fin g → ℂ, ∀ f, D f = ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left) V f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis <;> assumption)
