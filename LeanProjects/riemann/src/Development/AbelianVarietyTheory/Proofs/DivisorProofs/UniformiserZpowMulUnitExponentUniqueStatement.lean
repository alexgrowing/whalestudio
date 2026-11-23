import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUnique
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
theorem _root_.GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (a b : ℤ) (w w' : Vˣ), algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) = algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V) → a = b := by
  first | exact @GlobalTheory.exponent_uniformiser_unique | exact GlobalTheory.exponent_uniformiser_unique | (intros; apply GlobalTheory.exponent_uniformiser_unique <;> assumption)
