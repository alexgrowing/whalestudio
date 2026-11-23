import Mathlib

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSC

theorem iteratedDeriv_sum_on {ι : Type} (s : Finset ι) {U : Set ℂ} (hU : IsOpen U) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) (r : ℕ) :
    (∀ i ∈ s, DifferentiableOn ℂ (iteratedDeriv r (f i)) U) ∧
    EqOn (iteratedDeriv r (fun w => ∑ i ∈ s, f i w)) (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) U := by
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨hf, fun _ _ => rfl⟩
  | succ r ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨fun i hi => ?_, fun z hz => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (hd i hi).deriv hU
    · simp only [iteratedDeriv_succ]
      have hev : iteratedDeriv r (fun w => ∑ i ∈ s, f i w) =ᶠ[𝓝 z]
          (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) he
      rw [hev.deriv_eq]
      first
        | exact deriv_fun_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))
        | exact deriv_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))

theorem exists_int_elem {X : Type} [MeasurableSpace X] (ν : Measure X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (φ : X → V) (hφ : ∀ x, φ x ∈ W)
    (hint : ∀ l : V →ₗ[ℂ] ℂ, Integrable (fun x => l (φ x)) ν) :
    ∃ Φ ∈ W, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ x, l (φ x) ∂ν := by
  classical
  let b := Module.finBasis ℂ W
  choose cl hcl using fun j => LinearMap.exists_extend (b.coord j)
  have hc : ∀ j x, cl j (φ x) = b.repr ⟨φ x, hφ x⟩ j := by
    intro j x
    have := LinearMap.congr_fun (hcl j) ⟨φ x, hφ x⟩
    simpa using this
  have hrepr : ∀ x, φ x = ∑ j, cl j (φ x) • (b j : V) := by
    intro x
    have h1 := b.sum_repr ⟨φ x, hφ x⟩
    have h2 := congrArg (fun w : W => (w : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [hc]
    exact h2.symm
  refine ⟨∑ j, (∫ x, cl j (φ x) ∂ν) • (b j : V), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2,
    fun l => ?_⟩
  have e1 : ∀ x, l (φ x) = ∑ j, cl j (φ x) * l (b j) := by
    intro x
    conv_lhs => rw [hrepr x]
    simp [map_sum, map_smul, smul_eq_mul]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [e1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  · intro j _
    exact (hint (cl j)).mul_const _

end PositivityTheory.Rg.Sw.AbsSt.TSC
