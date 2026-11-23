import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulIterPartialDerivEqNegPowStatement

noncomputable section

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology

namespace GlobalTheory.HCA

theorem integrable_mul_of_continuousOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hcont : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
      have h0 : (fun x => f x * g x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact continuousAt_const.congr h0.symm
  exact hcont.integrable_of_hasCompactSupport (hgc.mul_left)

theorem dw_hasCompactSupport_tsupport {d : ℕ} (w : List (Fin d)) {f : E d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (dw w f) ∧ tsupport (dw w f) ⊆ tsupport f := by
  induction w with
  | nil => exact ⟨hf, subset_rfl⟩
  | cons j w ih =>
    refine ⟨ih.1.fderiv_apply (𝕜 := ℝ) (ev j), ?_⟩
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := dw w f) (ev j)).trans ih.2

theorem contDiff_mul_of_contDiffOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {b φ : E d → ℂ} (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : (fun y => b y * φ y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem weakSol_of_smooth :
    ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ),
      (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U →
      (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  intro d m U hU a ha u hu hap i φ hφ hc hs
  show ∫ x, u x * trOp m a φ x = 0
  have hψ : ∀ n w, ContDiff ℝ ∞ (fun y => a n w y * φ y) := fun n w =>
    contDiff_mul_of_contDiffOn_of_tsupport hU (ha n w) hφ hs
  have hψc : ∀ n w, HasCompactSupport (fun y => a n w y * φ y) := fun n w => hc.mul_left
  have hψs : ∀ n w, tsupport (fun y => a n w y * φ y) ⊆ U := fun n w =>
    (tsupport_mul_subset_right).trans hs
  have hI1 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) := by
    intro n w
    have hdc := dw_hasCompactSupport_tsupport (List.ofFn w) (hψc n w)
    have hcont : Continuous (dw (List.ofFn w) (fun y => a n w y * φ y)) := by
      have := (GlobalTheory.T.dw_contDiffOn_local_linear d Set.univ isOpen_univ (List.ofFn w)).1 _ (hψ n w).contDiffOn
      exact (contDiffOn_univ.1 this).continuous
    have := integrable_mul_of_continuousOn_of_tsupport hU hu.continuousOn
      (g := fun x => (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)
      (continuous_const.mul hcont) (hdc.1.mul_left)
      ((tsupport_mul_subset_right).trans (hdc.2.trans (hψs n w)))
    exact this
  have hI2 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => dw (List.ofFn w) u x * (a n w x * φ x)) := by
    intro n w
    exact integrable_mul_of_continuousOn_of_tsupport hU
      ((GlobalTheory.T.dw_contDiffOn_local_linear d U hU (List.ofFn w)).1 u hu).continuousOn (hψ n w).continuous (hψc n w) (hψs n w)
  have hterm : ∀ n (w : Fin n → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n w
    have hibp := GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow d U hU (List.ofFn w) u (fun y => a n w y * φ y) hu (hψ n w) (hψc n w)
      (hψs n w)
    rw [List.length_ofFn] at hibp
    have e1 : (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) =
        fun x => (-1 : ℂ) ^ n * (u x * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
      funext x; ring
    rw [e1, integral_const_mul, hibp, ← mul_assoc, ← mul_pow]
    norm_num
  have hsplit : (fun x => u x * trOp m a φ x) = fun x => ∑ n ∈ Finset.range (m + 1),
      ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
    funext x
    simp only [trOp, Finset.mul_sum]
  rw [hsplit, integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI1 n w))]
  have hin : ∀ n ∈ Finset.range (m + 1),
      ∫ x, ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, ∑ w : Fin n → Fin d, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n _
    rw [integral_finset_sum _ (fun w _ => hI1 n w), integral_finset_sum _ (fun w _ => hI2 n w)]
    exact Finset.sum_congr rfl fun w _ => hterm n w
  rw [Finset.sum_congr rfl hin,
    ← integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI2 n w))]
  have hzero : (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      dw (List.ofFn w) u x * (a n w x * φ x)) = fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : x ∈ U
    · have h := hap x hx
      have e : (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          dw (List.ofFn w) u x * (a n w x * φ x)) = apOp m a u x * φ x := by
        simp only [apOp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [e, h, zero_mul]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
      simp [h0]
  rw [hzero, integral_zero]

end GlobalTheory.HCA

end
