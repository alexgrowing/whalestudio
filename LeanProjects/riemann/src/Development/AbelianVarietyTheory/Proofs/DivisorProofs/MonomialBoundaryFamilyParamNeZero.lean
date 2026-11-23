import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoParam

theorem t_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  intro R _ _ Q m t gam hM hli hsym i hti
  have hdiag : ∀ y, gam i y y = 0 := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := hM y
    have h0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
    have hni : n i = 0 := by
      by_contra hne
      apply h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hti]; exact zero_pow hne), mul_zero]
    rw [hn i, hni]; simp
  have hz : gam i = 0 := by
    refine LinearMap.ext₂ fun y z => ?_
    have h := hdiag (y + z)
    simp only [map_add, LinearMap.add_apply, hdiag y, hdiag z, hsym i z y] at h
    simp only [LinearMap.zero_apply]
    omega
  exact hli.ne_zero i hz

end GlobalTheory.MonoParam
