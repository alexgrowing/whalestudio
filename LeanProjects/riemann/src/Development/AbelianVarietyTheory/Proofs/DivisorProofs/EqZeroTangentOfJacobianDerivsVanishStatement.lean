import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroTangentOfJacobianDerivsVanish
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_tangent_of_jacobian_derivs_vanish : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i) (g : Fin D → Γ(Y, K.bundle.U i)), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 → ∀ (w : Sp (DualNumber F) ⟶ Y) (hw : ⊤ ≤ w ⁻¹ᵁ K.bundle.U i), spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = z → w ≫ p = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p → (∀ a, (evalPt w _ hw (g a)).snd = 0) → w = spMap (TrivSqZeroExt.inlHom F F) ≫ z := by
  first | exact @GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian | exact GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian | (intros; apply GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian <;> assumption)
