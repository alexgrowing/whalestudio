import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem coefwise_add_of {T : (V n → ℂ) → ℂ} {F G : V n → Alt n}
    (h : ∀ S, T (fun x => (bas n).repr (F x) S + (bas n).repr (G x) S) =
      T (fun x => (bas n).repr (F x) S) + T (fun x => (bas n).repr (G x) S)) :
    coefwise T (fun x => F x + G x) = coefwise T F + coefwise T G := by
  simp only [coefwise, map_add, Finsupp.add_apply, h, add_smul, Finset.sum_add_distrib]

theorem coefwise_const_smul_of {T : (V n → ℂ) → ℂ} {F : V n → Alt n} (c : ℂ)
    (h : ∀ S, T (fun x => c • (bas n).repr (F x) S) = c • T (fun x => (bas n).repr (F x) S)) :
    coefwise T (fun x => c • F x) = c • coefwise T F := by
  simp only [coefwise, map_smul, Finsupp.smul_apply, h, Finset.smul_sum, smul_assoc]

theorem coefwise_sum_of {T : (V n → ℂ) → ℂ} {ι : Type} (t : Finset ι) {F : ι → V n → Alt n}
    (h : ∀ S, T (fun x => ∑ i ∈ t, (bas n).repr (F i x) S) = ∑ i ∈ t, T (fun x => (bas n).repr (F i x) S)) :
    coefwise T (fun x => ∑ i ∈ t, F i x) = ∑ i ∈ t, coefwise T (F i) := by
  simp only [coefwise, map_sum, Finsupp.finset_sum_apply, h, Finset.sum_smul]
  exact Finset.sum_comm

theorem delAt_dbarAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  intro n v
  refine ⟨fun F G hF hG => ⟨?_, ?_⟩, fun F c hF => ⟨?_, ?_⟩, fun ι t F hF => ⟨?_, ?_⟩, fun F G h => ⟨?_, ?_⟩,
    fun c => ⟨?_, ?_⟩⟩
  · rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.del_add (hF S) (hG S)]; rfl, mul_add]
  · rw [dbarAt, dbarAt, dbarAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.dbar_add (hF S) (hG S)]; rfl, mul_add]
  · rw [delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.del_const_smul c (hF S)]; rfl, mul_smul_comm]
  · rw [dbarAt, dbarAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.dbar_const_smul c (hF S)]; rfl, mul_smul_comm]
  · simp only [delAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.del_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · simp only [dbarAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.dbar_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · have e (S) : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.del_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [delAt, coefwise, e]
  · have e (S) : dbar (fun x => (bas n).repr (F x) S) v = dbar (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.dbar_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [dbarAt, coefwise, e]
  · simp [delAt, coefwise]
  · simp [dbarAt, coefwise]

end GlobalTheory.CxForm
