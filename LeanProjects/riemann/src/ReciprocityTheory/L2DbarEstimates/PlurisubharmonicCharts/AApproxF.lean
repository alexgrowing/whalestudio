import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem dbarAt_eq (j : ι) (F : ι → Y → ℂ) (y : Y) (ξ : Fin n → ℂ) :
    A.dbarAt j F y ξ = dbv (fderiv ℝ (F j ∘ (A.chart j).symm) (A.chart j y)) (WithLp.toLp 2 ξ) := by
  unfold dbarAt; rw [← sum_wdb_eq]

theorem dbarAt_eq_zero_of_holo (j : ι) (F : ι → Y → ℂ) (y : Y) {G : V n → ℂ}
    (hF : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G) (hG : DifferentiableAt ℂ G (A.chart j y))
    (ξ : Fin n → ℂ) : A.dbarAt j F y ξ = 0 := by
  rw [dbarAt_eq, hF.fderiv_eq, dbv_holo hG]

theorem mem_ovl {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) :
    A.chart j y ∈ ovl A.chart j i :=
  ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hi]⟩

theorem trans_contDiffAt {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ 2 ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) :=
  ((A.trans_contDiffOn j i).contDiffAt ((A.isOpen_ovl j i).mem_nhds (A.mem_ovl hj hi))).of_le
    (by norm_cast)

theorem levi_transfer (la : La) (f : Y → ℝ) (hf : A.SmoothFn f) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt j (fun x => A.ph la j x + f x) y ξ =
      A.leviAt i (fun x => A.ph la i x + f x) y
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)).ofLp := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : ContDiffAt ℂ 2 Φ v0 := A.trans_contDiffAt hj hi
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set h : V n → ℝ := fun u => A.ph la i ((A.chart i).symm u) + f ((A.chart i).symm u)
  have hh : ContDiffAt ℝ 2 h (Φ v0) := by
    rw [hΦv]
    exact (((A.smooth_ph la i).add (hf i)).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).of_le (by norm_cast)
  set G := A.g la j i ∘ (A.chart j).symm
  have hG : ContDiffAt ℂ 2 G v0 :=
    contDiffAt_two_of_holo (A.isOpen_ovl j i) (A.holo_g la j i) hv0
  have hG0 : G v0 ≠ 0 := by
    simp only [G, Function.comp, v0, (A.chart j).left_inv hj]; exact A.g_ne la j i y hj hi
  set u2 : Fin 2 → V n → ℝ := ![fun v => h (Φ v), fun v => Real.log (Complex.normSq (G v))]
  have hu2 : ∀ k, ContDiffAt ℝ 2 (u2 k) v0 := by
    intro k; fin_cases k
    · exact hh.comp v0 (hΦ.restrict_scalars ℝ)
    · exact (contDiffAt_normSq_comp hG).log (Complex.normSq_pos.2 hG0).ne'
  have hev : (fun v => ((A.ph la j ((A.chart j).symm v) + f ((A.chart j).symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((∑ k, u2 k v : ℝ) : ℂ) := by
    filter_upwards [hO] with v hv
    have hxj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hxi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    have hsy : (A.chart i).symm (Φ v) = (A.chart j).symm v := by
      simp only [Φ, Function.comp]; exact (A.chart i).left_inv hxi
    have hne : ‖A.g la j i ((A.chart j).symm v)‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la j i _ hxj hxi)
    simp only [Fin.sum_univ_two, u2, Matrix.cons_val_zero, Matrix.cons_val_one, h, hsy, G,
      Function.comp, A.ph_trans la j i _ hxj hxi, Complex.normSq_eq_norm_sq]
    push_cast; ring
  unfold leviAt
  rw [leviV_congr hev, leviV_ofReal_sum hu2, Fin.sum_univ_two]
  have e1 : u2 0 = fun v => h (Φ v) := rfl
  have e2 : u2 1 = fun v => Real.log (Complex.normSq (G v)) := rfl
  rw [e1, e2, leviV_log_normSq hG hG0, add_zero]
  have hc := leviV_comp (f := fun u => ((h u : ℝ) : ℂ)) (Φ := Φ) (y := v0) ?_ hΦ ξ
  · rw [show (fun v => ((h (Φ v) : ℝ) : ℂ)) = (fun u => ((h u : ℝ) : ℂ)) ∘ Φ from rfl, hc, hΦv]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hh

theorem dbar_local (β : V n → ℝ) (hβ : ContDiff ℝ ∞ β) (la' : La) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (F : ι → Y → ℂ) (c : ℂ)
    (hF : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] fun v =>
      c * (A.chiC i β ((A.chart j).symm v) : ℂ) * A.g la' j i ((A.chart j).symm v))
    (ξ : Fin n → ℂ) :
    A.dbarAt j F y ξ = c * A.g la' j i y *
      dbv (fderiv ℝ (fun u => (β u : ℂ)) (A.chart i y))
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)) := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : DifferentiableAt ℂ Φ v0 := (A.trans_contDiffAt hj hi).differentiableAt (by norm_num)
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set G := A.g la' j i ∘ (A.chart j).symm
  have hG : DifferentiableAt ℂ G v0 :=
    (A.holo_g la' j i).differentiableAt hO
  set βc : V n → ℂ := fun u => (β u : ℂ)
  have hβc : ContDiff ℝ ∞ βc := Complex.ofRealCLM.contDiff.comp hβ
  have hβd : DifferentiableAt ℝ βc (Φ v0) := hβc.differentiable (by norm_cast) _
  have hf1 : DifferentiableAt ℝ (fun v => c * (βc ∘ Φ) v) v0 :=
    (hβd.comp v0 (hΦ.restrictScalars ℝ)).const_mul c
  have hev : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 v0] fun v => c * (βc ∘ Φ) v * G v := by
    filter_upwards [hF, hO] with v hv hvO
    rw [hv, A.chiC_of_mem hvO.2]
    simp only [Function.comp, βc, G, Φ]
  rw [dbarAt_eq, hev.fderiv_eq, fderiv_fun_mul hf1 (hG.restrictScalars ℝ), dbv_add, dbv_smul,
    dbv_smul, dbv_holo hG, mul_zero, zero_add, fderiv_const_mul (hβd.comp v0 (hΦ.restrictScalars ℝ)),
    dbv_smul, dbv_comp hβd hΦ, hΦv]
  simp only [G, Function.comp, v0, (A.chart j).left_inv hj]
  ring

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
