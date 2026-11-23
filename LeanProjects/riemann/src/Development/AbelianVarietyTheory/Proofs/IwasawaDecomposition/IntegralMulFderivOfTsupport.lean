import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar

section Parts

variable {D : ℕ} {O : Set (V D)} {u χ : V D → ℝ}

theorem continuous_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ O) : Continuous fun v => u v * χ v :=
  (hu.mul hχ.continuousOn).continuous_of_tsupport_subset hO (tsupport_mul_subset_right.trans hs)

theorem integrable_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) : Integrable fun v => u v * χ v :=
  (continuous_mul_of_tsupport hO hu hχ hs).integrable_of_hasCompactSupport hc.mul_left

theorem contDiffOn_fderiv_apply (hO : IsOpen O) {n : ℕ∞ω} (hu : ContDiffOn ℝ (n + 1) u O) (a : V D) :
    ContDiffOn ℝ n (fun v => fderiv ℝ u v a) O :=
  (hu.fderiv_of_isOpen hO le_rfl).clm_apply contDiffOn_const

theorem integral_mul_fderiv_of_tsupport (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ χ v a = -∫ v, fderiv ℝ u v a * χ v :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 0) hu a).continuousOn
      hχ.continuous hc hs)
    (integrable_mul_of_tsupport hO hu.continuousOn
      ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ a)
      ((tsupport_fderiv_apply_subset ℝ a).trans hs))
    (integrable_mul_of_tsupport hO hu.continuousOn hχ.continuous hc hs)
    (fun _ hv => (hu.contDiffAt (hO.mem_nhds (hs hv))).differentiableAt one_ne_zero)
    (fun v _ => hχ.differentiable one_ne_zero v)

theorem fderiv_fderiv_apply {v : V D} (hu : ContDiffAt ℝ 2 u v) (a : V D) :
    fderiv ℝ (fun w => fderiv ℝ u w a) v a = fderiv ℝ (fderiv ℝ u) v a a := by
  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    (differentiableAt_const _)]
  simp

theorem continuousOn_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (a : V D) :
    ContinuousOn (fun v => fderiv ℝ (fderiv ℝ u) v a a) O :=
  (contDiffOn_fderiv_apply hO (n := 0) (contDiffOn_fderiv_apply hO (n := 1) hu a) a).continuousOn.congr
    fun _ hv => (fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv)) a).symm

theorem integral_mul_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ (fderiv ℝ χ) v a a = ∫ v, fderiv ℝ (fderiv ℝ u) v a a * χ v := by
  have hχ' : ContDiff ℝ 1 fun v => fderiv ℝ χ v a :=
    contDiffOn_univ.1 (contDiffOn_fderiv_apply isOpen_univ (n := 1) hχ.contDiffOn a)
  have h₁ := integral_mul_fderiv_of_tsupport hO (hu.of_le one_le_two) hχ' (hc.fderiv_apply ℝ a)
    ((tsupport_fderiv_apply_subset ℝ a).trans hs) a
  have h₂ := integral_mul_fderiv_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 1) hu a)
    (hχ.of_le one_le_two) hc hs a
  simp only [fderiv_fderiv_apply hχ.contDiffAt] at h₁
  rw [h₁, h₂, neg_neg]
  refine integral_congr_ae (.of_forall fun v => ?_)
  by_cases hv : v ∈ O
  · simp only [fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv))]
  · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero]

theorem exists_leviV_re_eq (ξ : Fin D → ℂ) : ∃ a b : V D, ∀ (f : V D → ℝ) (v : V D),
    ContDiffAt ℝ 2 f v → (leviV D (fun w => (f w : ℂ)) v ξ).re =
      4⁻¹ * (fderiv ℝ (fderiv ℝ f) v a a + fderiv ℝ (fderiv ℝ f) v b b) :=
  ⟨_, _, fun _ _ hf => by rw [← LocalMaximumSecondDerivative.leviV_re_eq hf ξ]; ring⟩

theorem continuousOn_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (ξ : Fin D → ℂ) :
    ContinuousOn (fun v => (leviV D (fun w => (u w : ℂ)) v ξ).re) O :=
  have ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  (continuousOn_const.mul ((continuousOn_fderiv_fderiv hO hu a).add
    (continuousOn_fderiv_fderiv hO hu b))).congr fun v hv => h u v (hu.contDiffAt (hO.mem_nhds hv))

theorem integral_mul_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (ξ : Fin D → ℂ) :
    ∫ v, u v * (leviV D (fun w => (χ w : ℂ)) v ξ).re =
      ∫ v, (leviV D (fun w => (u w : ℂ)) v ξ).re * χ v := by
  obtain ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  have I₁ (c : V D) : Integrable fun v => u v * fderiv ℝ (fderiv ℝ χ) v c c := by
    simp only [← fderiv_fderiv_apply hχ.contDiffAt]
    refine integrable_mul_of_tsupport hO hu.continuousOn ?_ ((hc.fderiv_apply ℝ c).fderiv_apply ℝ c)
      ((tsupport_fderiv_apply_subset ℝ c).trans ((tsupport_fderiv_apply_subset ℝ c).trans hs))
    simp only [fderiv_fderiv_apply hχ.contDiffAt]
    exact continuousOn_univ.1 (continuousOn_fderiv_fderiv isOpen_univ hχ.contDiffOn c)
  have I₂ (c : V D) : Integrable fun v => fderiv ℝ (fderiv ℝ u) v c c * χ v :=
    integrable_mul_of_tsupport hO (continuousOn_fderiv_fderiv hO hu c) hχ.continuous hc hs
  calc _ = ∫ v, 4⁻¹ * (u v * fderiv ℝ (fderiv ℝ χ) v a a + u v * fderiv ℝ (fderiv ℝ χ) v b b) :=
        integral_congr_ae (.of_forall fun v => by simp only [h χ v hχ.contDiffAt]; ring)
    _ = ∫ v, 4⁻¹ * (fderiv ℝ (fderiv ℝ u) v a a * χ v + fderiv ℝ (fderiv ℝ u) v b b * χ v) := by
        rw [integral_const_mul, integral_const_mul, integral_add (I₁ a) (I₁ b),
          integral_add (I₂ a) (I₂ b), integral_mul_fderiv_fderiv hO hu hχ hc hs,
          integral_mul_fderiv_fderiv hO hu hχ hc hs]
    _ = _ := by
        refine integral_congr_ae (.of_forall fun v => ?_)
        by_cases hv : v ∈ O
        · simp only [h u v (hu.contDiffAt (hO.mem_nhds hv))]; ring
        · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero, add_zero]

theorem nonneg_of_integral_mul_nonneg (hO : IsOpen O) (hu : ContinuousOn u O)
    (h : ∀ χ : V D → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      (∀ v, 0 ≤ χ v) → 0 ≤ ∫ v, u v * χ v) {v : V D} (hv : v ∈ O) : 0 ≤ u v := by
  by_contra hlt
  rw [not_le] at hlt
  have hn : O ∩ {w | u w < 0} ∈ 𝓝 v := inter_mem (hO.mem_nhds hv)
    ((hu.continuousAt (hO.mem_nhds hv)).eventually_lt continuousAt_const hlt)
  obtain ⟨χ, hs, hc, hχ, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hn
  have h0 (w) : 0 ≤ χ w := (hr ⟨w, rfl⟩).1
  have hs' := hs.trans inter_subset_left
  have hp : 0 < ∫ w, -u w * χ w :=
    (continuous_mul_of_tsupport hO hu.neg hχ.continuous hs').integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := v) hc.mul_left (fun w => by
        by_cases hw : w ∈ tsupport χ
        · exact mul_nonneg (neg_nonneg.2 (le_of_lt (hs hw).2)) (h0 w)
        · simp [image_eq_zero_of_notMem_tsupport hw]) (by simp [h1, hlt.ne])
  simp only [neg_mul, integral_neg] at hp
  linarith [h χ hχ hc hs' h0]

theorem posCurrent_iff_leviV (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) :
    PosCurrent O u ↔ ∀ v ∈ O, ∀ ξ, 0 ≤ (leviV D (fun w => (u w : ℂ)) v ξ).re := by
  have h2 {χ : V D → ℝ} (h : ContDiff ℝ ∞ χ) : ContDiff ℝ 2 χ := h.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨fun h v hv ξ => nonneg_of_integral_mul_nonneg hO (continuousOn_leviV_re hO hu ξ)
    (fun χ h₁ h₂ h₃ h₄ => (h.2 χ h₁ h₂ h₃ h₄ ξ).trans_eq (integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ)) hv,
    fun h => ⟨hu.continuousOn.locallyIntegrableOn hO.measurableSet, fun χ h₁ h₂ h₃ h₄ ξ => ?_⟩⟩
  rw [integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ]
  refine integral_nonneg fun v => ?_
  by_cases hv : v ∈ O
  · exact mul_nonneg (h v hv ξ) (h₄ v)
  · simp [image_eq_zero_of_notMem_tsupport fun h => hv (h₃ h)]

end Parts

namespace Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {ψ : Y.pts σ → ℝ}

theorem mSmooth.mPsh_iff_levi (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ) :
    mPsh Y σ Δ m ψ ↔ ∀ (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ), y ∈ c.e.source →
      y ∈ eqnSet σ Δ g → ∀ ξ, 0 ≤ c.levi (fun z => m.wt g z + ψ z) y ξ := by
  refine forall₂_congr fun c g => ?_
  have ho : IsOpen (chartDom c Δ g) := isOpen_over _ (isOpen_eqnSet Δ g)
  have hs : (Y.an σ).SmoothOn (eqnSet σ Δ g) fun z => m.wt g z + ψ z := fun j =>
    ((h.2 g).mono (fun _ hz => ⟨trivial, hz⟩) j).add (hψ.mono (subset_univ _) j)
  rw [and_iff_right (.of_forall fun _ _ => h.1 trivial)]
  refine (posCurrent_iff_leviV ho ((hs.chart (isOpen_eqnSet Δ g) c).of_le
    (WithTop.coe_le_coe.2 le_top))).trans ⟨fun H y hy hg => H _ (mem_over _ hy hg), fun H v hv ξ => ?_⟩
  have := H _ (c.e.map_target hv.1) hv.2 ξ
  rwa [AlgChart.levi, c.e.right_inv hv.1] at this

theorem mSmooth.levi_frame (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    {c : AlgChart Y.str σ Y.dim} {g g' : Y.Fnˣ} {y : Y.pts σ} (hy : y ∈ c.e.source)
    (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g') (ξ : Fin Y.dim → ℂ) :
    c.levi (fun z => m.wt g' z + ψ z) y ξ = c.levi (fun z => m.wt g z + ψ z) y ξ :=
  AnRead.levi_eq_of_add_log (R := Y.an σ) (f := fun z => m.wt g z + ψ z)
    ((isOpen_eqnSet Δ g).inter (isOpen_eqnSet Δ g'))
    (fun j => ((h.2 g).mono (fun _ hz => ⟨trivial, hz.1⟩) j).add (hψ.mono (subset_univ _) j))
    (holoOn_tv Δ g g') (fun _ hz => tv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [Met.wt_trans (h.1 trivial) hz.1 hz.2]; ring) hy ⟨hg, hg'⟩ ξ

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem mSmooth.mPsh_iff_semiPos (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    (hp : Presents Δ L r) :
    mPsh Y σ Δ m ψ ↔ ((m.toWeight h.posSet_eq hp).addFn ψ).SemiPos (Y.an σ) := by
  rw [h.mPsh_iff_levi hψ]
  refine ⟨fun H i c y hy ξ => H _ (r i) y hy.1 (ptsIn_subset_eqnSet hp i hy.2) ξ,
    fun H c g y hy hg ξ => ?_⟩
  have hi := mem_pick hp.isLB y
  rw [h.levi_frame hψ hy (ptsIn_subset_eqnSet hp _ hi) hg]
  exact H.chart ((h.isSmooth_toWeight hp).addFn hψ) hy hi ξ

theorem smoothOn_zero : (Y.an σ).SmoothOn univ (0 : Y.pts σ → ℝ) := fun _ => contDiffOn_const

end Var

end GlobalTheory.ProjVar
