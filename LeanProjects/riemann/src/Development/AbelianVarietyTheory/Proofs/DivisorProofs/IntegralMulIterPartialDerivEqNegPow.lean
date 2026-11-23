import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinear

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem integrable_mul_of_tsupport_subset {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hc : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hs h)
      have h0 : (fun x => f x * g x) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).1 hx'] with y hy
        simp [hy]
      exact (continuousAt_congr h0).2 continuousAt_const
  exact hc.integrable_of_hasCompactSupport hgc.mul_left

theorem integral_mul_partial_eq_neg {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (j : Fin d)
    {u ψ : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x (ev j) = - ∫ x, fderiv ℝ u x (ev j) * ψ x := by
  have hu1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (ev j)) U :=
    contDiffOn_dw_of_isOpen hU [j] u hu
  have hψ1 : Continuous (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsub : tsupport (fun x => fderiv ℝ ψ x (ev j)) ⊆ tsupport ψ := by
    refine (closure_mono ?_).trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := ψ))
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; exact hx (by simp [h])
  have hψ1c : HasCompactSupport (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E d →L[ℝ] ℂ => L (ev j)) (by simp)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_of_tsupport_subset hU hu1.continuousOn hψ.continuous hψc hψs
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ1 hψ1c (hsub.trans hψs)
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ.continuous hψc hψs
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hψs hx))).differentiableAt (by simp)
  · intro x _
    exact hψ.differentiable (by simp) x

theorem dw_contDiff_tsupport {d : ℕ} (w : List (Fin d)) {φ : E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dw w φ) ∧ tsupport (dw w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact ⟨hφ, subset_rfl⟩
  | cons j w ih =>
    refine ⟨(ih.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, ?_⟩
    refine (closure_mono ?_).trans ((tsupport_fderiv_subset (𝕜 := ℝ) (f := dw w φ)).trans ih.2)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; apply hx; show fderiv ℝ (dw w φ) x (ev j) = 0; simp [h]

theorem dw_append {d : ℕ} (w v : List (Fin d)) (f : E d → ℂ) : dw (w ++ v) f = dw w (dw v f) := by
  induction w with
  | nil => rfl
  | cons j w ih => funext x; show fderiv ℝ (dw (w ++ v) f) x (ev j) = _; rw [ih]; rfl

theorem dw_swap {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (a b : Fin d) {g : E d → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (dw [a, b] g) (dw [b, a] g) U := by
  intro x hx
  have hx' := hU.mem_nhds hx
  have hga : ContDiffAt ℝ ∞ g x := hg.contDiffAt hx'
  have hsym := hga.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.2 le_top : (2 : WithTop ℕ∞) ≤ ∞))
  have hd1 : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ g) x := by
    have := (contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg
    exact (this.2.contDiffAt hx').differentiableAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ g y (ev b)) x (ev a) = fderiv ℝ (fun y => fderiv ℝ g y (ev a)) x (ev b)
  rw [fderiv_clm_apply hdf (differentiableAt_const _), fderiv_clm_apply hdf (differentiableAt_const _)]
  have h0 : ∀ c : E d, fderiv ℝ (fun _ : E d => c) x = 0 := fun c => fderiv_const_apply c
  simp only [h0, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hsym _ _

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem dw_perm {d : ℕ} {U : Set (E d)} (hU : IsOpen U) {w₁ w₂ : List (Fin d)} (h : w₁.Perm w₂) :
    ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → Set.EqOn (dw w₁ u) (dw w₂ u) U := by
  induction h with
  | nil => intro u _; exact fun _ _ => rfl
  | cons j _ ih =>
    intro u hu z hz
    show fderiv ℝ _ z (ev j) = fderiv ℝ _ z (ev j)
    rw [((ih u hu).eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]
  | swap x y l =>
    intro u hu
    have e1 := dw_append [y, x] l u
    have e2 := dw_append [x, y] l u
    simp only [List.cons_append, List.nil_append] at e1 e2
    rw [e1, e2]
    exact dw_swap hU y x (contDiffOn_dw_of_isOpen hU l u hu)
  | trans _ _ ih₁ ih₂ => intro u hu; exact (ih₁ u hu).trans (ih₂ u hu)

theorem integral_mul_dw_eq_reverse {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d)) :
    ∀ (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w.reverse u x * φ x := by
  induction w with
  | nil => intro u φ _ _ _ _; simp [dw]
  | cons j w ih =>
    intro u φ hu hφ hφc hφs
    obtain ⟨hψ, hψs⟩ := dw_contDiff_tsupport w hφ
    have hψc : HasCompactSupport (dw w φ) := IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) hψs
    have step := integral_mul_partial_eq_neg hU j hu hψ hψc (hψs.trans hφs)
    have hu1 : ContDiffOn ℝ ∞ (dw [j] u) U := contDiffOn_dw_of_isOpen hU [j] u hu
    have ih' := ih (dw [j] u) φ hu1 hφ hφc hφs
    have e : dw w.reverse (dw [j] u) = dw (j :: w).reverse u := by
      rw [List.reverse_cons, dw_append]
    show ∫ x, u x * fderiv ℝ (dw w φ) x (ev j) = _
    rw [step]
    change -∫ x, dw [j] u x * dw w φ x = _
    rw [ih', e, List.length_cons, pow_succ]
    ring

theorem integral_mul_dw_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d))
    (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  intro d U hU w u φ hu hφ hφc hφs
  rw [integral_mul_dw_eq_reverse hU w u φ hu hφ hφc hφs]
  congr 2
  funext x
  by_cases hx : x ∈ U
  · rw [dw_perm hU (List.reverse_perm w) u hu hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
    simp [this]

end GlobalTheory.HCA
