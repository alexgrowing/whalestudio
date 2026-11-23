import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMemInvariantSubmodule

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem tensor_dual_action_apply_component (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (g : Fin n → M) (c : Fin n) :
    tensVd E a b g c = E a b (g c) - (if c = b then g a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem euler_tensor_dual_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem euler_tensor_dual_commute_gl_action (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  have hc : ∀ c, E d c (E a b (f c)) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) := by
    intro c
    have := congrArg (fun T : Module.End ℂ M => T (f c)) (hE d c a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    by_cases h1 : c = a <;> by_cases h2 : b = d <;> simp [h1, h2] <;> abel
  simp only [Module.End.mul_apply, euler_tensor_dual_apply, tensor_dual_action_apply_component, map_sub, map_neg, map_sum,
    sum_sub_distrib, hc, sum_add_distrib]
  by_cases hbd : b = d
  · subst hbd
    simp [apply_ite, Finset.sum_ite_eq']
    abel
  · have hdb : d ≠ b := Ne.symm hbd
    simp [hbd, hdb, apply_ite, Finset.sum_ite_eq']

theorem mem_pi_submodule_iff {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ Submodule.pi Set.univ (fun _ : Fin n => S) ↔ ∀ c, f c ∈ S := by
  simp [Submodule.mem_pi]

theorem dualTensorAction_mem {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S) (a b : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (c : Fin n) : tensVd E a b f c ∈ S := by
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hS a b _ (hf c)) ?_
  split_ifs
  · exact hf a
  · exact zero_mem _

theorem euler_tensor_dual_mem_of_stable {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (d : Fin n) : eeVd E f d ∈ S := by
  rw [euler_tensor_dual_apply]
  exact neg_mem (sum_mem fun c _ => hS d c _ (hf c))

theorem generated_submodule_stable_under_action (V : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  unfold genSub at *
  rw [Submodule.mem_sInf] at *
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem le_generatedSubmodule_dual (V : Submodule ℂ M) : V ≤ genSub E V := le_sInf fun _ hT => hT.1

theorem mem_euler_eigenspace_iff {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeVd E) S θ ↔ (∀ c, f c ∈ S) ∧ eeVd E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

theorem euler_eigenspace_stable_under_action (hE : IsGlRep E) {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {θ : ℝ} (a b : Fin n) {f : Fin n → M} (hf : f ∈ Xs (eeVd E) S θ) :
    tensVd E a b f ∈ Xs (eeVd E) S θ := by
  rw [mem_euler_eigenspace_iff] at hf ⊢
  refine ⟨dualTensorAction_mem hS a b hf.1, ?_⟩
  have := congrArg (fun T : Module.End ℂ (Fin n → M) => T f) (euler_tensor_dual_commute_gl_action hE a b)
  simp only [Module.End.mul_apply] at this
  rw [this, hf.2, map_smul]

end Alg

section Poly

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

theorem shifted_product_eq_aeval (A : Module.End ℂ Y) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C (((θ t : ℝ) : ℂ)))) := by
  unfold prodShift
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext t
  simp [Function.comp, Algebra.algebraMap_eq_smul_one]

theorem aeval_mem_invariant_submodule (A : Module.End ℂ Y) (p : Submodule ℂ Y) (hA : ∀ y ∈ p, A y ∈ p)
    (q : ℂ[X]) : ∀ y ∈ p, aeval A q y ∈ p := by
  first | exact UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule .. | (apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> first | assumption | infer_instance)

theorem aeval_commute_of_commute (A T : Module.End ℂ Y) (h : Commute A T) (q : ℂ[X]) :
    Commute (aeval A q) T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial k c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c T).mul_left (h.pow_left k)

end Poly

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
