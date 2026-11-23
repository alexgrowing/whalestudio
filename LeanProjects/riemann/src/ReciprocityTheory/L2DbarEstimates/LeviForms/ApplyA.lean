import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ap_db_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [db_eq_wdb n z e he j f x hx, db_eq_wdb n z e he j g x hx]
  apply wdb_congr
  have hzx : z x = e x := he hx
  rw [hzx]
  exact h.comp_tendsto (e.tendsto_symm hx)

theorem ap_smooth_of_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (h : ∀ x, ∃ G : M → ℂ, Smooth n z G ∧ f =ᶠ[𝓝 x] G) : Smooth n z f := by
  intro e he y hy
  obtain ⟨G, hG, hfG⟩ := h (e.symm y)
  apply ContDiffAt.contDiffWithinAt
  have hGa : ContDiffAt ℝ ∞ (G ∘ e.symm) y := (hG e he).contDiffAt (e.open_target.mem_nhds hy)
  exact hGa.congr_of_eventuallyEq (hfG.comp_tendsto (e.continuousAt_symm hy))

theorem ap_holo_d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) (k : Fin n) : Holo n z (d n z k f) := by
  intro e he
  have hh : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf e he
  have hcd : ContDiffOn ℂ ∞ (f ∘ e.symm) e.target :=
    contDiffOn_of_differentiableOn n _ _ e.open_target hh
  have hfd : DifferentiableOn ℂ (fun y => fderiv ℂ (f ∘ e.symm) y (bas n k)) e.target := by
    have h1 := (hcd.fderiv_of_isOpen e.open_target (m := ∞) (by exact_mod_cast le_top)).differentiableOn
      (by norm_num)
    exact h1.clm_apply (differentiableOn_const _)
  refine hfd.congr (fun y hy => ?_)
  simp only [Function.comp_apply]
  rw [d_comp_symm n z e he k f y hy]
  have hd := (hh.differentiableAt (e.open_target.mem_nhds hy)).hasFDerivAt
  rw [wd, (hd.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem ap_holo_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (hg : ∀ i, Holo n z (g i)) : Holo n z (jac n z g) := by
  intro e he
  have hA : ∀ i k, DifferentiableOn ℂ ((d n z k (g i)) ∘ e.symm) e.target :=
    fun i k => ap_holo_d n z (g i) (hg i) k e he
  have h1 : (jac n z g ∘ e.symm) = fun y => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, d n z i (g (σ i)) (e.symm y) := by
    funext y
    simp only [Function.comp_apply, jac, Matrix.det_apply, Matrix.of_apply, Units.smul_def,
      zsmul_eq_mul]
  rw [h1]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  intro y hy
  exact (HasFDerivWithinAt.finsetProd (fun i _ => ((hA (σ i) i) y hy).hasFDerivWithinAt)).differentiableWithinAt

theorem ap_cont_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have h := Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)
  exact h.congr (fun x => by simp)

theorem ap_smoothR_ev {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ) (hph : SmoothR n z ph) (r : ℝ) :
    SmoothR n z (ev n g ph r) := by
  have h1 : SmoothR n z (fun x => ∑ i ∈ Finset.univ, ‖g i x‖ ^ 2) :=
    smoothR_sum n z _ _ (fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i)))
  have h2 : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  have h3 := SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) (smoothR_const n z (1 / r ^ 2))
  convert h3 using 1
  funext x
  simp [ev, div_eq_mul_inv]

end ReciprocityTheory.L2DbarEstimates.I
