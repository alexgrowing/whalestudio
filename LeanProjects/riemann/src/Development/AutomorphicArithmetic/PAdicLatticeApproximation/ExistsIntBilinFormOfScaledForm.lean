import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormDenEqOneOnLattice
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_int_bilinForm_of_scaled_form :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ E : LinearMap.BilinForm ℤ X.lat, ∀ u w : X.lat, ((E u w : ℤ) : ℚ) = X.s * X.B (u : VQ D) (w : VQ D) := by
  intro p _ D X
  have h : ∀ u w : X.lat, (((X.s * X.B (u : VQ D) (w : VQ D)).num : ℤ) : ℚ)
      = X.s * X.B (u : VQ D) (w : VQ D) := fun u w =>
    Rat.coe_int_num_of_den_eq_one (UpperTheory.scaled_form_den_eq_one_on_lattice p D X u w u.2 w.2)
  refine ⟨LinearMap.mk₂ ℤ (fun u w : X.lat => (X.s * X.B (u : VQ D) (w : VQ D)).num)
    ?_ ?_ ?_ ?_, ?_⟩
  · intro u u' w
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add, LinearMap.add_apply, mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  · intro u w w'
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add, mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower, zsmul_eq_mul]
    ring
  · intro u w
    rw [LinearMap.mk₂_apply]
    exact h u w
