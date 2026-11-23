import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelabelMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_relabel_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (X : Data E r) (Di : Datum H) (τ : E →+* ℂ) (hτ : Formalism.L2.PjFree.relab c σ τ ∈ X.Ψ) (φ : Di.La ≃ₗ[𝓞 E] X.Λ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), r = Dw.p + Dw.q → X.p0 = Dw.q → τ (H.rt : E) = H.rt0 → (∀ ρ : E →+* ℂ, Formalism.L2.PjFree.relab c σ ρ ∈ X.Ψ ↔ ρ (H.rt : E) = H.rt0) → (∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → IsPerBasis Di x hm → ∃ b : ℂ, b ≠ 0 ∧ ∀ y ∈ X.dom, ∀ Q : Di.La →+ (Letter Dw → ℂ), (∀ v (z : Letter Dw), Q v z = Formalism.L2.PjFree.perFr X y (φ v : Fin r → E) (Formalism.L2.PjFree.relab c σ z.1) z.2) → perVal c σ τ x hm Q = b * GlobalTheory.FlatLine.horizGen ⟨_, hτ⟩ y := by
  first | exact @GlobalTheory.ShFam.PerDet.perVal_eq_horizGen | exact GlobalTheory.ShFam.PerDet.perVal_eq_horizGen | (intros; apply GlobalTheory.ShFam.PerDet.perVal_eq_horizGen <;> assumption)
