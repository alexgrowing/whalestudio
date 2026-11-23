import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartRescaleFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponentialChart_rescale_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | exact GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale <;> assumption)
