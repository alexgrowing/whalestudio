import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_representation_spectral_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  first | exact @GlobalTheory.UPel.HT.LieProj.lie_projectors | exact GlobalTheory.UPel.HT.LieProj.lie_projectors | (intros; apply GlobalTheory.UPel.HT.LieProj.lie_projectors <;> assumption)
