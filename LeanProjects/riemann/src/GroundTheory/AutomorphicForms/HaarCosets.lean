import Mathlib
import GroundTheory.AutomorphicForms.LocallyConstantCompact

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by
  set S := (finite_image_mk_tsupport K hf).toFinset with hS
  have hmeas : ∀ g : G, MeasurableSet (g • (K : Set G)) := fun g =>
    (K.isOpen.smul g).measurableSet
  have hfin : ∀ g : G, μ (g • (K : Set G)) ≠ ∞ := fun g =>
    (hKc.smul g).measure_lt_top.ne
  have hvol : ∀ g : G, μ.real (g • (K : Set G)) = μ.real (K : Set G) := fun g => by
    simp [Measure.real, measure_smul]
  have hdec := eq_sum_indicator_coset K hf hK
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · calc ∫ g, f g ∂μ
        = ∫ g, ∑ x ∈ S, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_congr_ae (Eventually.of_forall fun g => by
            rw [congrFun hdec g, Finset.sum_apply])
      _ = ∑ x ∈ S, ∫ g, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_finsetSum _ fun x _ =>
            (integrable_indicator_iff (hmeas _)).2 (integrableOn_const (hfin _))
      _ = μ.real (K : Set G) • ∑ x ∈ S, f x.out := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [integral_indicator_const _ (hmeas _), hvol]
  · intro x hx
    rw [hS, Set.Finite.coe_toFinset]
    exact ⟨x.out, subset_tsupport f hx, QuotientGroup.out_eq' x⟩

end Integral

end GroundTheory.Automorphic
