import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e
    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
