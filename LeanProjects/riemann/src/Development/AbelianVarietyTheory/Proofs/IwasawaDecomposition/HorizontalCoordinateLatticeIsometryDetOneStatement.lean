import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (Q : Di.La →+ (Letter Dw → ℂ)) (gm : Di.La ≃ₗ[𝓞 E] Di.La), IsPerBasis Di x hm → GoodPer c σ τ x hm Q → IsIsom Di gm → GoodPer c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) ∧ ‖perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom)‖ = ‖perVal c σ τ x hm Q‖ ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IsLev l Di gm → perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q) := by
  first | exact @GlobalTheory.ShFam.HorIso.perVal_isom | exact GlobalTheory.ShFam.HorIso.perVal_isom | (intros; apply GlobalTheory.ShFam.HorIso.perVal_isom <;> assumption)
