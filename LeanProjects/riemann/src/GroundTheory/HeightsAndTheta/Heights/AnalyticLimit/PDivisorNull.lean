import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StDivisorNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem DivisorNull.exists_chart_mem_alt {A : FinHolAtlas D X} (R : RegChartData A) (x : X) :
    ∃ j, x ∈ (R.ψ j).source ∧ R.ψ j x ∈ R.W j := by
  obtain ⟨j, hx, hW⟩ := R.cover x
  exact ⟨j, hx, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hW)))⟩

theorem DivisorNull.not_mem_Yo_iff {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.n) {y : X}
    (hy : y ∈ (R.ψ j).source) (hW : R.ψ j y ∈ R.W j) :
    y ∉ R.Yo ↔ ∏ i ∈ R.S j, R.ψ j y i = 0 := by
  have h := R.mem_Yo_iff j _ hW
  rw [(R.ψ j).left_inv hy] at h
  rw [h, not_not, Finset.prod_eq_zero_iff]
  rfl

theorem DivisorNull.isAnalyticSubset_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    A.IsAnalyticSubset R.Yoᶜ := by
  intro x
  obtain ⟨j, hx, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  refine ⟨(R.ψ j).source ∩ R.ψ j ⁻¹' R.W j, (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j), ⟨hx, hW⟩,
    1, fun _ y => ∏ i ∈ R.S j, R.ψ j y i, ?_, ?_⟩
  · intro _ k
    have hk := (R.compat j k).1
    show AnalyticOnNhd ℂ (fun z => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart k).symm) z i) _
    refine Finset.analyticOnNhd_fun_prod _ fun i _ z hz => ?_
    have hz' : AnalyticAt ℂ (R.ψ j ∘ (A.chart k).symm) z := hk z ⟨hz.1, hz.2.1⟩
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _).comp hz'
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hy, hs, hw⟩
      exact ⟨⟨hs, hw⟩, fun _ => (DivisorNull.not_mem_Yo_iff R j hs hw).1 hy⟩
    · rintro ⟨⟨hs, hw⟩, h⟩
      exact ⟨(DivisorNull.not_mem_Yo_iff R j hs hw).2 (h 0), hs, hw⟩

theorem DivisorNull.interior_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    interior R.Yoᶜ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUY, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨j, hxs, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  have hO : IsOpen (R.W j ∩ (R.ψ j).symm ⁻¹' U) := by
    have h2 := ((R.ψ j).isOpen_inter_preimage_symm hU).inter (R.isOpen_kappaOpenNeighbourhood j)
    convert h2 using 1
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨⟨R.W_subset j hz, hzU⟩, hz⟩
    · rintro ⟨⟨_, hzU⟩, hz⟩
      exact ⟨hz, hzU⟩
  have hxO : R.ψ j x ∈ R.W j ∩ (R.ψ j).symm ⁻¹' U := by
    refine ⟨hW, ?_⟩
    show (R.ψ j).symm (R.ψ j x) ∈ U
    rw [(R.ψ j).left_inv hxs]
    exact hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin D → ℂ := fun i => if R.ψ j x i = 0 then ((ε / 2 : ℝ) : ℂ) else R.ψ j x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : R.ψ j x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ ball (R.ψ j x) ε := by
    rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    intro i
    by_cases h : R.ψ j x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hε
  obtain ⟨hwW, hwU⟩ := hball hwb
  have hsrc : (R.ψ j).symm w ∈ (R.ψ j).source := (R.ψ j).map_target (R.W_subset j hwW)
  have hright : R.ψ j ((R.ψ j).symm w) = w := (R.ψ j).right_inv (R.W_subset j hwW)
  have hprod := (DivisorNull.not_mem_Yo_iff R j hsrc (by rw [hright]; exact hwW)).1 (hUY hwU)
  rw [hright, Finset.prod_eq_zero_iff] at hprod
  obtain ⟨i, -, hi⟩ := hprod
  exact hw0 i hi

theorem DivisorNull.proof : DivisorNull.Statement :=
  fun _ R => ⟨DivisorNull.isAnalyticSubset_compl_Yo R, DivisorNull.interior_compl_Yo R⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
