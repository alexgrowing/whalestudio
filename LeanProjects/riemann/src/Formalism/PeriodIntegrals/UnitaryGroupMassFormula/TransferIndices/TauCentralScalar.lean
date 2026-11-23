import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.TIW

open PI.Dv

section Theta

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)

def theta (M : Module.End K (T.W s)) : MonoidAlgebra K G :=
  ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s y⁻¹ * M)) • MonoidAlgebra.of K G y

theorem theta_one : theta T s 1 = eS T s := by simp [theta, eS]

theorem theta_add (M N : Module.End K (T.W s)) : theta T s (M + N) = theta T s M + theta T s N := by
  simp [theta, mul_add, add_smul, Finset.sum_add_distrib]

theorem theta_smul (c : K) (M : Module.End K (T.W s)) : theta T s (c • M) = c • theta T s M := by
  simp only [theta, Finset.smul_sum, smul_smul, mul_smul_comm, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring_nf

theorem theta_zero : theta T s 0 = 0 := by simp [theta]

theorem theta_eq' (M : Module.End K (T.W s)) : theta T s M =
    ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (M * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by
  simp only [theta, LinearMap.trace_mul_comm K (T.tau s _) M]

theorem mul_eS (z : MonoidAlgebra K G) : z * eS T s = theta T s ((T.tau s).asAlgebraHom z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp [theta_zero]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, theta_add]
  | single g r =>
    rw [Representation.asAlgebraHom_single, theta_smul, eS, Finset.mul_sum, theta, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulLeft, mul_smul_comm, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      mul_one, smul_smul]
    rw [← map_mul, mul_inv_rev, inv_mul_cancel_right, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring

theorem eS_mul (z : MonoidAlgebra K G) : eS T s * z = theta T s ((T.tau s).asAlgebraHom z) := by
  rw [theta_eq']
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, hx, hy, map_add]
    simp only [add_mul, map_add, mul_add, add_smul, Finset.sum_add_distrib]
  | single g r =>
    rw [Representation.asAlgebraHom_single, eS, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulRight, smul_mul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      one_mul, smul_smul, smul_mul_assoc, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    rw [← map_mul, mul_inv_rev, mul_inv_cancel_left, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring

theorem eS_central (z : MonoidAlgebra K G) : eS T s * z = z * eS T s := by
  rw [eS_mul, mul_eS]

theorem mul_eS_eq (z z' : MonoidAlgebra K G)
    (hz : (T.tau s).asAlgebraHom z = (T.tau s).asAlgebraHom z') : z * eS T s = z' * eS T s := by
  rw [mul_eS, mul_eS, hz]

theorem tau_central_scalar (c : MonoidAlgebra K G) (hc : ∀ z, c * z = z * c) :
    ∃ μ : K, (T.tau s).asAlgebraHom c = μ • 1 := by
  have hmem : (T.tau s).asAlgebraHom c ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [← map_mul, ← map_mul, hc z]
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  exact ⟨μ, by rw [← hμ, Algebra.algebraMap_eq_smul_one]⟩

theorem tau_eS [CharZero K] : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T s (eS T s) (eS_central T s)
  set d := Module.finrank K (T.W s) with hd
  have hd0 : (d : K) ≠ 0 := by
    have : 0 < d := Module.finrank_pos
    exact_mod_cast this.ne'
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

  set Ξ : Module.End K (Module.End K (T.W s)) := ∑ y : G,
    (((d : K) / ((Fintype.card G : ℕ) : K)) •
      ((LinearMap.trace K (T.W s)) ∘ₗ LinearMap.mulLeft K (T.tau s y⁻¹))).smulRight (T.tau s y) with hΞ
  have hΞapp : ∀ M, Ξ M = (T.tau s).asAlgebraHom (theta T s M) := by
    intro M
    rw [hΞ, theta, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, Representation.asAlgebraHom_of, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]
  have hΞμ : Ξ = μ • LinearMap.id := by
    apply LinearMap.ext; intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [hΞapp, ← mul_eS, map_mul, hμ]
    simp
  have htr := congrArg (LinearMap.trace K _) hΞμ
  rw [hΞ, map_sum, map_smul, LinearMap.trace_id, Module.finrank_linearMap] at htr
  simp only [LinearMap.trace_smulRight, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at htr
  have : μ = 1 := by
    rw [← hd] at htr
    push_cast at htr
    field_simp at htr
    first
    | exact htr.symm
    | exact htr
    | (have h2 : (d : K) * d ≠ 0 := mul_ne_zero hd0 hd0
       apply mul_right_cancel₀ h2
       linear_combination -htr)
  rw [hμ, this, one_smul]

theorem eS_idem [CharZero K] : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, theta_one]

end Theta

end PI.Dv.TIW
