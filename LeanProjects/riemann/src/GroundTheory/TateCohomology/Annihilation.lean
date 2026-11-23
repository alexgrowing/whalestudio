import Mathlib
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.TateLow
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem norm_apply_of_mem_invariants (A : Rep.{u} R G) {a : A} (ha : a ∈ A.ρ.invariants) :
    A.ρ.norm a = Fintype.card G • a := by
  rw [Representation.mem_invariants] at ha
  simp [Representation.norm, LinearMap.sum_apply, ha]

theorem card_smul_tateCohomology_zero (A : Rep.{u} R G) (x : tateCohomology A 0) :
    Fintype.card G • x = 0 := by
  let e := ((tateCohomologyZeroIso R G).app A).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (normRangeInvariants A) (e x)
  rw [← hy]
  have h : (Submodule.Quotient.mk (Fintype.card G • y) :
      A.ρ.invariants ⧸ normRangeInvariants A) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_normRangeInvariants_iff]
    exact ⟨y, by rw [norm_apply_of_mem_invariants A y.2]; rfl⟩
  rw [Submodule.Quotient.mk_smul] at h
  exact h

private theorem card_smul_succ {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A n), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A (n + 1)) : Fintype.card G • x = 0 := by
  let e := (coindShiftIso A n).toLinearEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_nsmul, h, map_zero]

private theorem card_smul_pred {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A (n + 1)), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A n) : Fintype.card G • x = 0 := by
  let e := (indShiftIso A n).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero, h]

theorem card_smul_tateCohomology (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by
  induction n using Int.induction_on generalizing A with
  | zero => exact card_smul_tateCohomology_zero A x
  | succ n ih => exact card_smul_succ (fun A x => ih A x) A x
  | pred n ih =>
    refine card_smul_pred ?_ A x
    rw [sub_add_cancel]
    exact ih

end GroundTheory.GroupCoh
