import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMoveMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

namespace GlobalTheory

theorem sval_eq_zero_of_indep_comb :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  intro R R' _ _ f X Y Y' π _ π' p H L hL K _ φ ε M _ β hβ d hd m Z r z J hJ
  let e := (Fintype.equivFin M).symm
  have key := ThetaSpecialise.sec_indep H ε (φ := φ) (φ' := fun k => p ≫ φ k) (fun _ => rfl) (fun i => β (e i))
    (fun a ha i => by
      have := hβ (fun m => a (e.symm m)) (by
        rw [← ha, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply]) (e i)
      simpa only [Equiv.symm_apply_apply] using this)
    (fun i => d (e i)) (sec_ext' hL fun y J hJ => by
      rw [sval_sum' hJ, sval_zero' hJ, ← hd y J hJ, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sval_smul' hJ]
      exact congrArg₂ (· * ·) (by rw [Category.id_comp])
        ((sval_pullOver H.w _ _ _ hJ).trans (by rw [Category.id_comp]))) (e.symm m)
  rw [Equiv.apply_symm_apply] at key
  exact (congrArg (fun s => sval s r z J) key).trans (sval_zero' (π := π) hJ r)

end GlobalTheory
