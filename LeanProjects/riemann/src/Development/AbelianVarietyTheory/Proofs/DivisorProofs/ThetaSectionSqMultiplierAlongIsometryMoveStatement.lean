import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMove
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  first | exact @GlobalTheory.GeoLevel.theta_move_sq | exact GlobalTheory.GeoLevel.theta_move_sq | (intros; apply GlobalTheory.GeoLevel.theta_move_sq <;> assumption)
