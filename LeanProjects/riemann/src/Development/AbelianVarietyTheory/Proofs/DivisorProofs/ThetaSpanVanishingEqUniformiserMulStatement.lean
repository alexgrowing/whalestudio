import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanVanishingEqUniformiserMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  first | exact @GlobalTheory.Desc.ModPi.modPi | exact GlobalTheory.Desc.ModPi.modPi | (intros; apply GlobalTheory.Desc.ModPi.modPi <;> assumption)
