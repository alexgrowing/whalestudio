import ReciprocityTheory.DualLattices.SubgroupFreenessStatement
import ReciprocityTheory.DualLattices.HasColengthEqPowMulPow

namespace ReciprocityTheory.PGsh.L2

theorem h3 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩

end ReciprocityTheory.PGsh.L2
