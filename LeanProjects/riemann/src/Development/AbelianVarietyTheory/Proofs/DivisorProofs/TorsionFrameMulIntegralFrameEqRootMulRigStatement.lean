import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  first | exact @GlobalTheory.USep.FrameRoot.frame_mul_eq_root | exact GlobalTheory.USep.FrameRoot.frame_mul_eq_root | (intros; apply GlobalTheory.USep.FrameRoot.frame_mul_eq_root <;> assumption)
