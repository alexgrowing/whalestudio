import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryDiscMapEmbeddingFixed
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_disc_map_embedding_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0}) (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n a : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X')), a ≤ n → IsHolTo (Metric.ball 0 1) p → (∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F))) → (∀ u ∈ Flat.punct n a 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)), x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) → ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (h : Sp C.R ⟶ X'), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model | exact GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model <;> assumption)
