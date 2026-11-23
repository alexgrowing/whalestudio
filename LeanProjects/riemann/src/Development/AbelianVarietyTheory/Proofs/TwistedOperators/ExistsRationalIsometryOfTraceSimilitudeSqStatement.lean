import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_similitude_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | exact GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | (intros; apply GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude <;> assumption)
