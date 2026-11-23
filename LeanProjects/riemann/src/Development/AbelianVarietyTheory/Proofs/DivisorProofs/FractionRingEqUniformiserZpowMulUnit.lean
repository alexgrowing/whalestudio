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

namespace GlobalTheory

theorem DVR.fractionRing_eq_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  intro V _ _ _ ϖ hϖ y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨n₁, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n₂, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(n₁ : ℤ) - n₂, u₁ * u₂⁻¹, ?_⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact hϖ.ne_zero
  have hu : ∀ u : Vˣ, algebraMap V (FractionRing V) (u : V) ≠ 0 := fun u => by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact u.ne_zero
  have h2 := hu u₂
  have h1 := hu u₁
  have key : algebraMap V (FractionRing V) ((u₂⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u₂ : V))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, key, zpow_sub₀ hϖ0, zpow_natCast]
  field_simp

end GlobalTheory
