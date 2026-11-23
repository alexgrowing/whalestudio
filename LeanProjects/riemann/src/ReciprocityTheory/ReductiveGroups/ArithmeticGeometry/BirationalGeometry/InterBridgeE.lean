import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem analyticAt_lift_chart (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((R.A.chart j).symm v)) u := by
  rw [analyticAt_pi_iff]
  intro p
  exact R.holo x p j u hu

theorem brQ_eq_local {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  obtain ⟨c, hc0, hc⟩ := R.compat x z z ⟨hz, R.mem_U z⟩
  have hseg : segre (R.lift x z) = (∏ k, c k) • segre (R.lift z z) := by
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, hc, Finset.prod_mul_distrib]
  have hC : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  funext i
  simp only [brQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hC]

theorem analyticAt_segre_lift (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hseg : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u := by
    rw [analyticAt_pi_iff]
    intro i
    simp only [segre]
    have hp := Finset.analyticAt_prod (Finset.univ : Finset K) fun k _ => (analyticAt_pi_iff.mp hl) ⟨k, i k⟩
    exact hp.congr (Filter.Eventually.of_forall fun v => by simp [Finset.prod_apply])
  have := ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hseg
  exact this

theorem analyticAt_brQ (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  have hxs : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemT : R.A.chart j x ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hnhd : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x ∈ 𝓝 (R.A.chart j x) := by
    apply Filter.inter_mem ((R.A.chart j).open_target.mem_nhds hmemT)
    apply ((R.A.chart j).continuousAt_symm hmemT).preimage_mem_nhds
    rw [hxs]
    exact (R.isOpen_U x).mem_nhds (R.mem_U x)
  have heq : (fun v => fun i : Fin e => Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ /
      Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) =ᶠ[𝓝 (R.A.chart j x)]
      brQ R Ψ ∘ (R.A.chart j).symm := by
    filter_upwards [hnhd] with v hv
    exact (brQ_eq_local R Ψ hv.2).symm
  refine AnalyticAt.congr ?_ heq
  have hs := analyticAt_segre_lift R Ψ x j ⟨hmemT, by simp [hxs, R.mem_U x]⟩
  have hcomp := analyticAt_pi_iff.mp hs
  rw [analyticAt_pi_iff]
  intro i
  apply AnalyticAt.div (hcomp i.succ) (hcomp 0)
  simpa [hxs] using h0

theorem brQ_image_null_of
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  have hsub : brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}) ⊆
      ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) '' ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.A.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]
      exact hx
    · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · intro v hv
    have hvs : (R.A.chart j).symm v ∈ (R.A.chart j).source := (R.A.chart j).map_target hv.1
    have hA := analyticAt_brQ R Ψ ((R.A.chart j).symm v) j hvs hv.2.2
    rw [(R.A.chart j).right_inv hv.1] at hA
    exact (hA.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · exact measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)) (hS j)

end ReciprocityTheory.ChartRestriction.G.Geo
