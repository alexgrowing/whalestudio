import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt (f g : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) =
      _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul, show (fun z ↦ f z + g z) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.add_apply, mul_add]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_const_fun (c : ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => ?_]
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_congr_germ (f g : (I → ℂ) → ℂ) (h : f =ᶠ[𝓝 0] g) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem map_taylor_algHom (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ) :
    ψ (taylor N t f) = taylor N (fun i ↦ ψ (t i)) f := by
  unfold taylor
  simp only [map_sum, map_smul, map_prod]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span (f : (I → ℂ) → ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t) := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ']
  have h0 : ∑ s : Fin 0 → I, ((↑(Nat.factorial 0))⁻¹ * (iteratedFDeriv ℂ 0 f 0)
      fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a) = algebraMap ℂ D (f 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h0, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun s _ => ?_
  rw [Algebra.smul_def, Fin.prod_univ_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s 0, rfl⟩))

end

set_option autoImplicit false in
open Filter Topology in

theorem _root_.GlobalTheory.PeriodFamily.taylor_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • _root_.GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (_root_.GlobalTheory.PeriodFamily.taylor N t f) = _root_.GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  intro I _ _ D _ _ N t
  refine ⟨fun f g hf hg => _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t f g hf hg,
    fun c f hf => ?_, _root_.GlobalTheory.PeriodFamily.taylor_const_fun N t,
    _root_.GlobalTheory.PeriodFamily.taylor_congr_germ N t, fun D' _ _ ψ f => ?_,
    _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t⟩
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl,
      iteratedFDeriv_const_smul_apply' hf.contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, smul_smul, mul_left_comm]
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    simp [map_sum, map_prod]

end GlobalTheory.PeriodFamily
