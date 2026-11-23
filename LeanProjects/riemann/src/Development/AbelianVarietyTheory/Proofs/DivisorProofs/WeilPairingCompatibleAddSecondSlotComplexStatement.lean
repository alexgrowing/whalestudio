import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddRightComplex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_add_second_position_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.weilEq_mul_right_add | exact GlobalTheory.weilEq_mul_right_add | (intros; apply GlobalTheory.weilEq_mul_right_add <;> assumption)
