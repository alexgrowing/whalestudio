import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.ContractPowSuccMem

noncomputable section

universe u

namespace PI.KoszulExact

variable {R : Type u} [CommRing R] {D : ℕ}

theorem proj_kills_Li_pow (i : Fin D) (p : ℕ) (x : ExteriorAlgebra R (Fin D → R))
    (hx : x ∈ Li R D i ^ p) :
    CliffordAlgebra.contractLeft (LinearMap.proj i : (Fin D → R) →ₗ[R] R) x = 0 := by
  rw [Li_eq_map] at hx
  refine contract_pow_eq_zero _ _ ?_ p x hx
  intro m hm
  have hle : Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i}) ≤ LinearMap.ker (LinearMap.proj i : (Fin D → R) →ₗ[R] R) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := fun h => by subst h; exact lt_irrefl (i : ℕ) hk
    simp [hne]
  exact hle hm

theorem uniq (i : Fin D) (p q : ℕ) (u v : ExteriorAlgebra R (Fin D → R))
    (hu : u ∈ Li R D i ^ p) (hv : v ∈ Li R D i ^ q) (h : u + eb R i * v = 0) : v = 0 ∧ u = 0 := by
  have h1 := congrArg (CliffordAlgebra.contractLeft (LinearMap.proj i : (Fin D → R) →ₗ[R] R)) h
  rw [map_add, map_zero, proj_kills_Li_pow i p u hu, zero_add, eb,
    CliffordAlgebra.contractLeft_ι_mul, ← eb, proj_kills_Li_pow i q v hv, mul_zero, sub_zero] at h1
  simp only [LinearMap.coe_proj, Function.eval, Pi.single_eq_same, one_smul] at h1
  refine ⟨h1, ?_⟩
  rw [h1, mul_zero, add_zero] at h
  exact h

end PI.KoszulExact
