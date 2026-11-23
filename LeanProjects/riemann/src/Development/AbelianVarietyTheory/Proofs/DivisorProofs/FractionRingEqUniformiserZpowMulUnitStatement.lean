import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  first | exact @GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | exact GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | (intros; apply GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit <;> assumption)
