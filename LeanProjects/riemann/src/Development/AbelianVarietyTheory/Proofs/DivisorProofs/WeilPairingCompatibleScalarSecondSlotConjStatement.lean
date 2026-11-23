import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingSmulRightConj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.CM.ActRight.weilEq_act_right | exact GlobalTheory.CM.ActRight.weilEq_act_right | (intros; apply GlobalTheory.CM.ActRight.weilEq_act_right <;> assumption)
