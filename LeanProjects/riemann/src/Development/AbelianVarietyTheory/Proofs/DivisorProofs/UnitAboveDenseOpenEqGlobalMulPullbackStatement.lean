import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback : ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  first | exact @GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | exact GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | (intros; apply GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU <;> assumption)
