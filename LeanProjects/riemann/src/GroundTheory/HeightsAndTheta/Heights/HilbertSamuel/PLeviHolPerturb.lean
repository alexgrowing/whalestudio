import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

noncomputable section

namespace LeviHolPerturb

variable {J : Type} [Fintype J]

theorem hasDerivAt_of_contDiffAt_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (deriv f t) t) ∧ HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually (by simp)] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  · have h1 : ContDiffAt ℝ 1 (fun t => fderiv ℝ f t 1) 0 :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact (h1.differentiableAt one_ne_zero).hasDerivAt

theorem deriv_deriv_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    deriv (deriv fun t => f t * g t) 0 =
      deriv (deriv f) 0 * g 0 + 2 * (deriv f 0 * deriv g 0) + f 0 * deriv (deriv g) 0 := by
  obtain ⟨hf1, hf2⟩ := hasDerivAt_of_contDiffAt_two hf
  obtain ⟨hg1, hg2⟩ := hasDerivAt_of_contDiffAt_two hg
  have hev : deriv (fun t => f t * g t) =ᶠ[𝓝 0] fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hf1, hg1] with t h1 h2
    exact (h1.mul h2).deriv
  rw [hev.deriv_eq]
  refine ((hf2.mul hg1.self_of_nhds).add (hf1.self_of_nhds.mul hg2)).deriv.trans ?_
  ring

theorem deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F} {z : J → ℂ}
    (hf : DifferentiableAt ℝ f z) (e : J → ℂ) :
    deriv (fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ f z e := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hz0.symm).deriv

theorem deriv_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
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

theorem contDiffAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => f (z + s • e)) 0 := by
  have hl : ContDiffAt ℝ 2 (fun s : ℝ => z + s • e) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  exact ContDiffAt.comp (g := f) (0 : ℝ) (by simpa using hf) hl

theorem sndDeriv_I_I {φ : (J → ℂ) → ℂ} {z : J → ℂ} (hφ : AnalyticAt ℂ φ z) (a : J → ℂ) :
    fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ φ) z a a := by
  have hR : AnalyticAt ℝ φ z := hφ.restrictScalars
  have hT : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z :=
    (((hR.contDiffAt (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hlin : ∀ a b : J → ℂ, fderiv ℝ (fderiv ℝ φ) z a (Complex.I • b) =
      Complex.I • fderiv ℝ (fderiv ℝ φ) z a b := by
    intro a b
    have h1 := hT.clm_apply (hasFDerivAt_const (Complex.I • b) z)
    have h2 := (hT.clm_apply (hasFDerivAt_const b z)).const_smul Complex.I
    have hev : (fun y => fderiv ℝ φ y (Complex.I • b)) =ᶠ[𝓝 z]
        (fun y => Complex.I • fderiv ℝ φ y b) := by
      filter_upwards [hφ.eventually_analyticAt] with y hy
      rw [hy.differentiableAt.fderiv_restrictScalars ℝ]
      simp
    have h3 := (h1.congr_of_eventuallyEq hev.symm).unique h2
    have := congrArg (fun L => L a) h3
    simpa using this
  have hsymm : IsSymmSndFDerivAt ℝ φ z := (hR.contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  calc fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a)
      = Complex.I • fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) a := hlin _ _
    _ = Complex.I • fderiv ℝ (fderiv ℝ φ) z a (Complex.I • a) := by rw [hsymm]
    _ = Complex.I • Complex.I • fderiv ℝ (fderiv ℝ φ) z a a := by rw [hlin]
    _ = - fderiv ℝ (fderiv ℝ φ) z a a := by rw [smul_smul, Complex.I_mul_I]; simp

theorem line_key {X : ℝ → ℝ} {A Φ : ℝ → ℂ} (hX : ContDiffAt ℝ 2 X 0) (hA : ContDiffAt ℝ 2 A 0)
    (hΦ : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : deriv Φ 0 = 0) :
    deriv (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 = 0 ∧
      deriv (deriv fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 =
        2 * X 0 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
  have hg : (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) =
      fun t => X t * (2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) := by
    funext t
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  rw [hg]
  obtain ⟨hX1, hX2⟩ := hasDerivAt_of_contDiffAt_two hX
  obtain ⟨hA1, hA2⟩ := hasDerivAt_of_contDiffAt_two hA
  obtain ⟨hΦ1, hΦ2⟩ := hasDerivAt_of_contDiffAt_two hΦ
  have hN2 : ContDiffAt ℝ 2 (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 :=
    (contDiffAt_const.mul (hA.inner ℝ hΦ)).add (hΦ.inner ℝ hΦ)
  have hN0 : (2 * inner ℝ (A 0) (Φ 0) + inner ℝ (Φ 0) (Φ 0) : ℝ) = 0 := by simp [h0]
  have hNd : HasDerivAt (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 0 := by
    have h := ((hA1.self_of_nhds.inner ℝ hΦ1.self_of_nhds).const_mul 2).add
      (hΦ1.self_of_nhds.inner ℝ hΦ1.self_of_nhds)
    exact h.congr_deriv (by simp [h0, h1])
  have hev : deriv (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) =ᶠ[𝓝 0]
      fun t => 2 * (inner ℝ (A t) (deriv Φ t) + inner ℝ (deriv A t) (Φ t)) +
        (inner ℝ (Φ t) (deriv Φ t) + inner ℝ (deriv Φ t) (Φ t)) := by
    filter_upwards [hA1, hΦ1] with t ha hp
    exact (((ha.inner ℝ hp).const_mul 2).add (hp.inner ℝ hp)).deriv
  have hNdd : deriv (deriv fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 =
      2 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
    rw [hev.deriv_eq]
    have h := ((((hA1.self_of_nhds.inner ℝ hΦ2).add (hA2.inner ℝ hΦ1.self_of_nhds)).const_mul 2).add
      ((hΦ1.self_of_nhds.inner ℝ hΦ2).add (hΦ2.inner ℝ hΦ1.self_of_nhds)))
    refine h.deriv.trans ?_
    simp [h0, h1]
  have key := deriv_deriv_mul hX hN2
  beta_reduce at key
  refine ⟨?_, ?_⟩
  · refine (hX1.self_of_nhds.mul hNd).deriv.trans ?_
    simp [h0]
  · rw [key, hNdd, hN0, hNd.deriv]
    ring

theorem along {ξ : (J → ℂ) → ℝ} {a φ : (J → ℂ) → ℂ} {z : J → ℂ} (hξ : ContDiffAt ℝ 2 ξ z)
    (ha : AnalyticAt ℂ a z) (hφ : AnalyticAt ℂ φ z) (hφ0 : φ z = 0)
    (hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z) (v : J → ℂ)
    (hv : fderiv ℂ φ z v = 0) :
    fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v = 0 ∧
      fderiv ℝ (fderiv ℝ fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v v =
        2 * ξ z * inner ℝ (a z) (fderiv ℝ (fderiv ℝ φ) z v v) := by
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hz0 : z + (0 : ℝ) • v = z := by rw [zero_smul, add_zero]
  have h0 : (fun t : ℝ => φ (z + t • v)) 0 = 0 := by simp [hφ0]
  have h1 : deriv (fun t : ℝ => φ (z + t • v)) 0 = 0 := by
    rw [deriv_line (hφR.differentiableAt (by norm_num)) v,
      hφ.differentiableAt.fderiv_restrictScalars ℝ]
    simpa using hv
  obtain ⟨k1, k2⟩ := line_key (X := fun t => ξ (z + t • v)) (A := fun t => a (z + t • v))
    (Φ := fun t => φ (z + t • v)) (contDiffAt_line hξ v) (contDiffAt_line haR v)
    (contDiffAt_line hφR v) h0 h1
  refine ⟨?_, ?_⟩
  · rw [← deriv_line (hu.differentiableAt (by norm_num)) v]
    exact k1
  · rw [← deriv_deriv_line hu v, ← deriv_deriv_line hφR v]
    rw [show ξ z = ξ (z + (0 : ℝ) • v) by rw [hz0], show a z = a (z + (0 : ℝ) • v) by rw [hz0]]
    exact k2

theorem proof : LeviHolPerturb.Statement := by
  intro J _ ξ a φ z w hξ ha hφ hφ0 hdφ
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z :=
    hξ.mul (((haR.add hφR).norm_sq ℝ).sub (haR.norm_sq ℝ))
  have hw := along hξ ha hφ hφ0 hu w hdφ
  have hIw := along hξ ha hφ hφ0 hu (Complex.I • w) (by rw [map_smul, hdφ, smul_zero])
  refine ⟨hu, by simp [hφ0], hw.1, hIw.1, ?_⟩
  unfold leviForm
  rw [hw.2, hIw.2, sndDeriv_I_I hφ w, inner_neg_right]
  ring

end LeviHolPerturb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
