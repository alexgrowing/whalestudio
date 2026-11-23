import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.SimpleRoot

theorem exists_analytic_simple_root
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ)
    (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) w₀)
    (h0 : ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0)
    (h1 : ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0) :
    ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧
      AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W,
        ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  set F : E × ℂ → ℂ := fun p => ∑ j ∈ Finset.range (n + 1), c j p.1 * p.2 ^ j with hFdef
  have hFa : AnalyticAt ℂ F (w₀, τ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((hc j).comp analyticAt_fst).mul (analyticAt_snd.pow j)
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) F (w₀, τ₀) := hFa.contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set d : ℂ := ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) with hd_def
  have hd : HasDerivAt (fun τ => F (w₀, τ)) d τ₀ :=
    HasDerivAt.fun_sum (u := Finset.range (n + 1)) (A := fun j τ => c j w₀ * τ ^ j)
      (A' := fun j => (j : ℂ) * c j w₀ * τ₀ ^ (j - 1)) fun j _ => by
        rw [show (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) = c j w₀ * ((j : ℂ) * τ₀ ^ (j - 1)) by ring]
        exact (hasDerivAt_pow j τ₀).const_mul (c j w₀)
  have hfd : HasFDerivAt (fun τ => F (w₀, τ))
      ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) τ₀ :=
    hFa.differentiableAt.hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right w₀ τ₀)
  have heq : (fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d :=
    hfd.unique hd.hasFDerivAt
  have if₂ : ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d h1), ?_⟩
    ext
    simp
  set g := cdf.implicitFunction pn if₂ with hg_def
  have hg : AnalyticAt ℂ g w₀ := (cdf.contDiffAt_implicitFunction pn if₂).analyticAt
  obtain ⟨V₂, W, hV₂o, hw₀V₂, hWo, hτ₀W, hsub⟩ :=
    mem_nhds_prod_iff'.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨{w | AnalyticAt ℂ g w} ∩ V₂, W, g, (isOpen_analyticAt ℂ g).inter hV₂o, ⟨hg, hw₀V₂⟩, hWo, hτ₀W,
    fun w hw => hw.1, ?_⟩
  intro w hw τ hτ hroot
  have hmem := hsub (Set.mk_mem_prod hw.2 hτ)
  simp only [Set.mem_ofPred_eq] at hmem
  have h' : F (w, τ) = F (w₀, τ₀) := by
    change (∑ j ∈ Finset.range (n + 1), c j w * τ ^ j) = ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j
    rw [hroot, h0]
  exact (hmem.1 h').symm

end GlobalTheory.CompanionTheory.SimpleRoot
