import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

namespace RegularizedCurvature

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian

set_option linter.unusedSectionVars false

section Second

theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} (hg : IsLocalMin g 0) (hc : ContinuousAt g 0) :
    0 ≤ deriv (deriv g) 0 := by
  by_contra hneg
  push Not at hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hg.deriv_eq_zero hc
  have hev : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hg, hmax] with s h1 h2
    exact le_antisymm h2 h1
  have h2 : deriv (deriv g) 0 = 0 := by
    rw [hev.deriv.deriv_eq]
    simp
  linarith

variable {J : Type} [Fintype J]

theorem deriv_deriv_line {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv

theorem sndDeriv_nonneg_of_isLocalMin {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hmin : IsLocalMin f z) (e : J → ℂ) : 0 ≤ fderiv ℝ (fderiv ℝ f) z e e := by
  rw [← deriv_deriv_line hf e]
  have hc : Continuous fun s : ℝ => z + s • e := continuous_const.add (continuous_id.smul continuous_const)
  have hz : z + (0 : ℝ) • e = z := by simp
  refine deriv_deriv_nonneg_of_isLocalMin ?_ ?_
  · have h : IsLocalMin f (z + (0 : ℝ) • e) := by rw [hz]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun s : ℝ => z + s • e) (b := 0) h hc.continuousAt
  · exact ContinuousAt.comp_of_eq hf.continuousAt hc.continuousAt hz

theorem levi_le_of_le {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z)
    (hle : ∀ᶠ y in 𝓝 z, ψ y ≤ φ y) (heq : ψ z = φ z) (w : J → ℂ) :
    ReciprocityTheory.AnForm.levi ψ z w ≤ ReciprocityTheory.AnForm.levi φ z w := by
  have hf : ContDiffAt ℝ 2 (fun y => φ y + (-1) * ψ y) z := hφ.add (contDiffAt_const.mul hψ)
  have hmin : IsLocalMin (fun y => φ y + (-1) * ψ y) z := by
    filter_upwards [hle] with y hy
    simp only [heq]
    linarith
  have h1 := sndDeriv_nonneg_of_isLocalMin hf hmin w
  have h2 := sndDeriv_nonneg_of_isLocalMin hf hmin (Complex.I • w)
  have h3 : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => φ y + (-1) * ψ y) z w := by
    unfold ReciprocityTheory.AnForm.levi
    exact div_nonneg (add_nonneg h1 h2) (by norm_num)
  rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hφ hψ w] at h3
  linarith

theorem levi_const (c : ℝ) (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => c) z w = 0 := by
  simp [ReciprocityTheory.AnForm.levi]

end Second

section Holo

variable {J : Type} [Fintype J]

theorem analyticAt_eval_map (p : MvPolynomial J ℤ) (z : J → ℂ) :
    AnalyticAt ℂ (fun y : J → ℂ => MvPolynomial.eval y (MvPolynomial.map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) v).analyticAt z)

theorem log_norm_pluriharmonic {T : (J → ℂ) → ℂ} {z : J → ℂ} (hT : AnalyticAt ℂ T z) (h0 : T z ≠ 0)
    (w : J → ℂ) : ContDiffAt ℝ 2 (fun y => Real.log ‖T y‖) z ∧
      ReciprocityTheory.AnForm.levi (fun y => Real.log ‖T y‖) z w = 0 := by
  have hG : AnalyticAt ℂ (fun y => Complex.log (T y / T z)) z := by
    refine (hT.div analyticAt_const h0).clog ?_
    show T z / T z ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  have hev : (fun y => Real.log ‖T y‖) =ᶠ[𝓝 z]
      fun y => (Complex.log (T y / T z)).re + Real.log ‖T z‖ * (fun _ : J → ℂ => (1 : ℝ)) y := by
    filter_upwards [hT.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hy) (norm_ne_zero_iff.mpr h0)]
    ring
  have hre : ContDiffAt ℝ 2 (fun y => (Complex.log (T y / T z)).re) z := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z (hG.restrictScalars.contDiffAt (n := 2))
    convert h using 1
    funext y
    simp
  have hc : ContDiffAt ℝ 2 (fun _ : J → ℂ => (1 : ℝ)) z := contDiffAt_const
  refine ⟨(hre.add (contDiffAt_const.mul hc)).congr_of_eventuallyEq hev, ?_⟩
  rw [ReciprocityTheory.AnForm.levi_congr hev w, ReciprocityTheory.AnForm.levi_add_smul _ hre hc w,
    ReciprocityTheory.AnForm.levi_re_analytic hG w, levi_const]
  ring

end Holo

section LogSum

theorem log_sum_ineq {x x0 ε : ℝ} (hx : 0 < x) (hx0 : 0 < x0) (hε : 0 < ε) :
    Real.log (x0 + ε) - x0 / (x0 + ε) * Real.log x0 ≤
      Real.log (x + ε) - x0 / (x0 + ε) * Real.log x := by
  have hS : 0 < x0 + ε := by linarith
  have hl : 0 < x0 / (x0 + ε) := div_pos hx0 hS
  have hm : 0 < ε / (x0 + ε) := div_pos hε hS
  have hlm : x0 / (x0 + ε) + ε / (x0 + ε) = 1 := by
    rw [← add_div, div_self hS.ne']
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr (div_pos hx hx0))
    (Set.mem_Ioi.mpr one_pos) hl.le hm.le hlm
  have harg : x0 / (x0 + ε) * (x / x0) + ε / (x0 + ε) * 1 = (x + ε) / (x0 + ε) := by
    field_simp
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconc
  rw [harg, Real.log_div (by linarith) hS.ne', Real.log_div hx.ne' hx0.ne'] at hconc
  nlinarith

variable {J : Type} [Fintype J]

theorem levi_logSum {h : (J → ℂ) → ℝ} {T : (J → ℂ) → ℂ} {Φ : (J → ℂ) → ℝ} {z : J → ℂ} {ε : ℝ}
    (hφ : ContDiffAt ℝ 2 (fun y => Real.log (h y)) z) (hpos : ∀ᶠ y in 𝓝 z, 0 < h y)
    (hT : AnalyticAt ℂ T z) (hε : 0 < ε) (hΦ : ContDiffAt ℝ 2 Φ z)
    (hform : ∀ y, Φ y = Real.log (h y) + Real.log ((‖T y‖ / h y) ^ 2 + ε) / 2) (w : J → ℂ) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
      μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (h y)) z w ≤ ReciprocityTheory.AnForm.levi Φ z w := by
  have hc1 : ContDiffAt ℝ 2 (fun _ : J → ℂ => (1 : ℝ)) z := contDiffAt_const
  by_cases h0 : T z = 0
  ·
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hψ : ContDiffAt ℝ 2 (fun y => Real.log (h y) + Real.log ε / 2 * (fun _ : J → ℂ => (1 : ℝ)) y) z :=
      hφ.add (contDiffAt_const.mul hc1)
    have hle := levi_le_of_le hΦ hψ (Eventually.of_forall fun y => by
        rw [hform y]
        have : Real.log ε ≤ Real.log ((‖T y‖ / h y) ^ 2 + ε) :=
          Real.log_le_log hε (by nlinarith [sq_nonneg (‖T y‖ / h y)])
        linarith) (by rw [hform z, h0]; simp) w
    rw [ReciprocityTheory.AnForm.levi_add_smul _ hφ hc1 w, levi_const] at hle
    linarith
  ·
    obtain ⟨hg1, hlg⟩ := log_norm_pluriharmonic hT h0 w
    have hz : 0 < h z := hpos.self_of_nhds
    set x0 : ℝ := (‖T z‖ / h z) ^ 2 with hx0
    have hx0p : 0 < x0 := pow_pos (div_pos (norm_pos_iff.mpr h0) hz) 2
    have hS : 0 < x0 + ε := by linarith
    set l : ℝ := x0 / (x0 + ε) with hl
    set m : ℝ := ε / (x0 + ε) with hm
    have hlm : l + m = 1 := by rw [hl, hm, ← add_div, div_self hS.ne']
    have hm0 : 0 < m := div_pos hε hS
    have hl0 : 0 < l := div_pos hx0p hS
    set c : ℝ := Φ z - m * Real.log (h z) - l * Real.log ‖T z‖ with hc
    refine ⟨m, hm0.le, by linarith, ?_⟩
    have hA : ContDiffAt ℝ 2 (fun y => c + m * Real.log (h y)) z := contDiffAt_const.add (contDiffAt_const.mul hφ)
    have hψ : ContDiffAt ℝ 2 (fun y => (c + m * Real.log (h y)) + l * Real.log ‖T y‖) z :=
      hA.add (contDiffAt_const.mul hg1)

    have hid : ∀ y, 0 < h y → T y ≠ 0 → Φ y - m * Real.log (h y) - l * Real.log ‖T y‖ =
        (Real.log ((‖T y‖ / h y) ^ 2 + ε) - l * Real.log ((‖T y‖ / h y) ^ 2)) / 2 := by
      intro y hy hTy
      rw [hform y, Real.log_pow, Real.log_div (norm_ne_zero_iff.mpr hTy) hy.ne']
      have : m = 1 - l := by linarith
      rw [this]
      push_cast
      ring
    have hle := levi_le_of_le hΦ hψ (by
        filter_upwards [hpos, hT.continuousAt.eventually_ne h0] with y hy hTy
        have hxy : 0 < (‖T y‖ / h y) ^ 2 := pow_pos (div_pos (norm_pos_iff.mpr hTy) hy) 2
        have e1 := hid y hy hTy
        have e2 := hid z hz h0
        have key := log_sum_ineq hxy hx0p hε
        rw [← hx0] at e2
        rw [hc]
        linarith) (by rw [hc]; ring) w
    have hlevi : ReciprocityTheory.AnForm.levi (fun y => (c + m * Real.log (h y)) + l * Real.log ‖T y‖) z w =
        m * ReciprocityTheory.AnForm.levi (fun y => Real.log (h y)) z w := by
      rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y => c + m * Real.log (h y)) l hA hg1 w, hlg,
        ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => c) m contDiffAt_const hφ w, levi_const]
      ring
    rw [hlevi] at hle
    exact hle

end LogSum

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_noZeroBlock : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

def F (k : K) (y : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))

theorem blk_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    (fun i => z ⟨k, i⟩ : ι k → ℂ) ≠ 0 := by
  obtain ⟨i, hi⟩ := hz k
  exact fun h0 => hi (congrFun h0 i)

theorem rho_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) :=
  (fsMetric (ι k)).pos _ (blk_ne hz k)

theorem contDiffAt_F {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk]
  exact hφ.comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt

theorem levi_F_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) hφ]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (blk_ne hz k) _

end Blocks

section Levi

variable {J : Type} [Fintype J]

theorem levi_add_sum {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have heq : (fun y => g y + ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => g y' + ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq, ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (hf a) w, ih.2, Finset.sum_insert ha]
    exact ⟨ih.1.add (contDiffAt_const.mul (hf a)), by ring⟩

theorem laplacian_line_eq_levi {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by
  have h1 : ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) (fun _ => 0) (Pi.single 0 1) =
      Δ (fun t : ℂ => φ (z + t • v)) 0 / 4 :=
    ReciprocityTheory.AnForm.A.leviOne (fun t : ℂ => φ (z + t • v)) 0
  set L : (Fin 1 → ℂ) →L[ℂ] (J → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight v with hL
  have hτ : AnalyticAt ℂ (fun w => z + L w) (fun _ => 0) :=
    analyticAt_const.add (L.analyticAt _)
  have hτ0 : z + L (fun _ => (0 : ℂ)) = z := by
    simp [hL]
  have hcomp : (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) = φ ∘ fun w => z + L w := by
    funext w
    simp [hL]
  have hD : fderiv ℂ (fun w => z + L w) (fun _ => 0) (Pi.single 0 1) = v := by
    rw [((L.hasFDerivAt).const_add z).fderiv]
    simp [hL]
  have hφ' : ContDiffAt ℝ 2 φ (z + L (fun _ => 0)) := by
    rw [hτ0]
    exact hφ
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp _ hτ hφ', hτ0, hD] at h1
  linarith

end Levi

end RegularizedCurvature

end GroundTheory.Heights₂.Heights.Inter
