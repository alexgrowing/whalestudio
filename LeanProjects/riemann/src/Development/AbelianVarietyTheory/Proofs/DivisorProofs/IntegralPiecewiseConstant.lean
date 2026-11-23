import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem integral_eq_tsum_of_const_on_partition_measure_one :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) {ι : Type} [Countable ι] (S : ι → Set X),
    (∀ k, MeasurableSet (S k)) → Pairwise (Function.onFun Disjoint S) → (∀ x, ∃ k, x ∈ S k) → (∀ k, μ (S k) = 1) →
    ∀ (g : ι → ℂ), Summable (fun k => ‖g k‖) → ∀ f : X → ℂ, (∀ k, ∀ x ∈ S k, f x = g k) →
    ∫ x, f x ∂μ = ∑' k, g k := by
  intro X _ μ ι _ S hS hd hcov hμ g hg f hf
  have hU : (⋃ k, S k) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact hcov x
  have hreal : ∀ k, μ.real (S k) = 1 := fun k => by simp [Measure.real, hμ k]
  have hint : ∀ k, IntegrableOn f (S k) μ := fun k =>
    (integrableOn_const (by simp [hμ k])).congr_fun (fun x hx => (hf k x hx).symm) (hS k)
  have hval : ∀ k, ∫ x in S k, f x ∂μ = g k := fun k => by
    rw [setIntegral_congr_fun (hS k) (fun x hx => hf k x hx), setIntegral_const, hreal k, one_smul]
  have hnorm : ∀ k, ∫ x in S k, ‖f x‖ ∂μ = ‖g k‖ := fun k => by
    rw [setIntegral_congr_fun (hS k) (g := fun _ => ‖g k‖) (fun x hx => by simp only [hf k x hx]), setIntegral_const,
      hreal k, one_smul]
  have hI : IntegrableOn f (⋃ k, S k) μ :=
    integrableOn_iUnion_of_summable_integral_norm hint (by simpa only [hnorm] using hg)
  rw [← setIntegral_univ, ← hU, integral_iUnion hS hd hI]
  exact tsum_congr hval

end GlobalTheory
