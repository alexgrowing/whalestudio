import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmObjHomOfType_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
    (x : Fin p → 𝓞 E), ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  first | exact @GlobalTheory.FlatCM.HomIndep.phiP_independent | exact GlobalTheory.FlatCM.HomIndep.phiP_independent | (intros; apply GlobalTheory.FlatCM.HomIndep.phiP_independent <;> assumption)
