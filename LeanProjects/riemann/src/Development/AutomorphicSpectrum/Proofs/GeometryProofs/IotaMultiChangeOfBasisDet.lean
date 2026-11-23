import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Lat

theorem wedge_matrix_mul_family (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  let L : (Fin n → Ω) →ₗ[Ω] V := (Pi.basisFun Ω (Fin n)).constr Ω e
  have hL : ∀ c : Fin n → Ω, L c = ∑ j, c j • e j := fun c => by
    simp [L, Module.Basis.constr_apply_fintype]
  have hLe : (fun i => L (Pi.basisFun Ω (Fin n) i)) = e := funext fun i => by simp [L]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => ?_
  let A : (Fin n → Ω) [⋀^Fin n]→ₗ[Ω] Ω :=
    (f.compAlternatingMap (exteriorPower.ιMulti Ω n (M := V))).compLinearMap L
  have h := congrArg (fun g => g (fun i => P i))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin n)) A)
  simp only [AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h
  have h1 : A (fun i => P i) = f (exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j)) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
    funext i
    exact hL _
  have h2 : A (Pi.basisFun Ω (Fin n)) = f (exteriorPower.ιMulti Ω n e) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
  have h3 : (Matrix.of fun i => P i) = P := rfl
  rw [h1, h2, h3] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.CompanionTheory.Ar.Lat
