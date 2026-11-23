import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.MemOOfIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.AsAlgebraHomMemSpan

noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section H

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)

theorem epsS_eq_smul (P : Pair K G) : epsS P = ((Nat.card P.H : ℕ) : K) • eps P := by
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [eps_eq, smul_smul, mul_inv_cancel₀ this, one_smul]

theorem tau_eps_idem (P : Pair K G) : τ.asAlgebraHom (eps P) * τ.asAlgebraHom (eps P) = τ.asAlgebraHom (eps P) := by
  rw [← map_mul, eps_idem]

theorem trace_mem_of_intR (z : MonoidAlgebra K G) (hz : IntR z) :
    LinearMap.trace K W (τ.asAlgebraHom z) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hz' := intEl_of_intR z hz
  have key : LinearMap.trace K W (τ.asAlgebraHom z) ∈ (algebraMap (𝓞 K) K).range := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, map_sum]
    refine Subring.sum_mem _ fun g _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Subring.mul_mem _ (RingHom.mem_range.mpr (hz' g)) (RingHom.mem_range.mpr (trace_tau_mem τ g))
  exact RingHom.mem_range.mp key

theorem sandwich (P0 : Pair K G) (h1 : Module.finrank K (LinearMap.range (τ.asAlgebraHom (eps P0))) = 1)
    (z : MonoidAlgebra K G) :
    τ.asAlgebraHom (epsS P0 * z * eps P0) =
      LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) • τ.asAlgebraHom (eps P0) := by
  have hL : τ.asAlgebraHom (epsS P0 * z * eps P0) = ((Nat.card P0.H : ℕ) : K) •
      (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z * τ.asAlgebraHom (eps P0)) := by
    rw [epsS_eq_smul, smul_mul_assoc, smul_mul_assoc, map_smul, map_mul, map_mul]
  have hR : LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) = ((Nat.card P0.H : ℕ) : K) *
      LinearMap.trace K W (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z) := by
    rw [epsS_eq_smul, smul_mul_assoc, map_smul, map_smul, map_mul, smul_eq_mul]
  rw [hL, hR, rank_one_sandwich _ (tau_eps_idem τ P0) h1, smul_smul]

end H

section Absorb

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem absorb_eps (T : GoodSet K G) (s : T.S) (Q R : Pair K G) (z : MonoidAlgebra K G) :
    eps Q * eS T s * (epsS Q * z) * (eps R * eS T s) = epsS Q * z * (eps R * eS T s) := by
  calc eps Q * eS T s * (epsS Q * z) * (eps R * eS T s)
      = eps Q * (eS T s * (epsS Q * z * eps R)) * eS T s := by simp only [mul_assoc]
    _ = eps Q * ((epsS Q * z * eps R) * eS T s) * eS T s := by rw [eS_central]
    _ = (eps Q * epsS Q) * z * eps R * (eS T s * eS T s) := by simp only [mul_assoc]
    _ = epsS Q * z * (eps R * eS T s) := by rw [eps_mul_epsS, eS_idem]; simp only [mul_assoc]

end Absorb

end PI.Dv.TIW
