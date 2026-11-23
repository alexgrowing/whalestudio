import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCalc
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff
open Finset

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

theorem pd_mul {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) :
    pd i (fun y ↦ f y * g y) = fun y ↦ pd i f y * g y + f y * pd i g y := by
  funext y
  have h := ((hf.differentiable (by simp) y).hasFDerivAt).mul
    ((hg.differentiable (by simp) y).hasFDerivAt)
  rw [pd]
  change (fderiv ℝ (f * g) y) (ev i) = _
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, pd]
  ring

theorem hsD_mul_le (k : ℕ) : ∀ {f g : 𝔼 → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → ∀ x : 𝔼,
    hsD k (fun y ↦ f y * g y) x ≤
      ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  induction k with
  | zero =>
    intro f g hf hg x
    simp [hsD_zero]
  | succ k ih =>
    intro f g hf hg x
    have hfg : ContDiff ℝ ∞ (fun y ↦ f y * g y) := hf.mul hg
    set S : ℕ × ℕ → Fin n → ℝ := fun ij i ↦ (k.choose ij.1 : ℝ) *
      (hsD ij.2 g x * hsD ij.1 (pd i f) x + hsD ij.1 f x * hsD ij.2 (pd i g) x) with hS
    have hi : ∀ i, |hsD k (pd i (fun y ↦ f y * g y)) x| ≤
        ∑ ij ∈ antidiagonal k, 1 * S ij i := by
      intro i
      rw [abs_of_nonneg (hsD_nonneg _ _ _), pd_mul hf hg i]
      calc hsD k (fun y ↦ pd i f y * g y + f y * pd i g y) x
          ≤ hsD k (fun y ↦ pd i f y * g y) x + hsD k (fun y ↦ f y * pd i g y) x :=
            hsD_add_le ((contDiff_pd hf i).mul hg) (hf.mul (contDiff_pd hg i)) k x
        _ ≤ (∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * hsD ij.1 (pd i f) x * hsD ij.2 g x) +
            ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 (pd i g) x :=
            add_le_add (ih (contDiff_pd hf i) hg x) (ih hf (contDiff_pd hg i) x)
        _ = ∑ ij ∈ antidiagonal k, 1 * S ij i := by
            rw [← sum_add_distrib]
            refine sum_congr rfl fun ij _ ↦ ?_
            simp only [hS]
            ring
    have hsucc : ∀ h : 𝔼 → ℂ, ContDiff ℝ ∞ h → ∀ j,
        Real.sqrt (∑ i, hsD j (pd i h) x ^ 2) = hsD (j + 1) h x :=
      fun h hh j ↦ by rw [← hsD_succ_sq hh, Real.sqrt_sq (hsD_nonneg _ _ _)]
    rw [← hsucc _ hfg k]
    calc Real.sqrt (∑ i, hsD k (pd i (fun y ↦ f y * g y)) x ^ 2)
        ≤ ∑ ij ∈ antidiagonal k, 1 * Real.sqrt (∑ i, S ij i ^ 2) :=
          sqrt_sum_sq_le_sum _ _ _ _ (fun _ _ ↦ zero_le_one) hi
      _ ≤ ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) *
            (hsD ij.2 g x * hsD (ij.1 + 1) f x + hsD ij.1 f x * hsD (ij.2 + 1) g x) := by
          refine sum_le_sum fun ij _ ↦ ?_
          rw [one_mul]
          simp only [hS]
          rw [sqrt_sum_sq_const_mul, abs_of_nonneg (by positivity)]
          gcongr
          calc Real.sqrt (∑ i, (hsD ij.2 g x * hsD ij.1 (pd i f) x +
                hsD ij.1 f x * hsD ij.2 (pd i g) x) ^ 2)
              ≤ Real.sqrt (∑ i, (hsD ij.2 g x * hsD ij.1 (pd i f) x) ^ 2) +
                Real.sqrt (∑ i, (hsD ij.1 f x * hsD ij.2 (pd i g) x) ^ 2) :=
                sqrt_sum_sq_add_le _ _
            _ = hsD ij.2 g x * hsD (ij.1 + 1) f x + hsD ij.1 f x * hsD (ij.2 + 1) g x := by
                rw [sqrt_sum_sq_const_mul, sqrt_sum_sq_const_mul, hsucc f hf, hsucc g hg,
                  abs_of_nonneg (hsD_nonneg _ _ _), abs_of_nonneg (hsD_nonneg _ _ _)]
      _ = ∑ ij ∈ antidiagonal (k + 1), ((k + 1).choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
          have e := sum_antidiagonal_choose_succ_mul (R := ℝ) (fun i j ↦ hsD i f x * hsD j g x) k
          simp_rw [mul_assoc]
          rw [e]
          have e2 : ∀ ij ∈ antidiagonal k, (k.choose ij.2 : ℝ) = (k.choose ij.1 : ℝ) := by
            intro ij hij
            rw [HasAntidiagonal.mem_antidiagonal] at hij
            rw [← hij, Nat.choose_symm_add]
          have e3 : ∑ ij ∈ antidiagonal k, (k.choose ij.2 : ℝ) * (hsD (ij.1 + 1) f x * hsD ij.2 g x) =
              ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * (hsD (ij.1 + 1) f x * hsD ij.2 g x) :=
            sum_congr rfl fun ij hij ↦ by rw [e2 ij hij]
          rw [e3, ← sum_add_distrib]
          refine sum_congr rfl fun ij _ ↦ ?_
          ring

theorem hsD_sub_const {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) {k : ℕ} (hk : 0 < k)
    (x : 𝔼) : hsD k (fun y ↦ f y - c) x = hsD k f x := by
  have h : ∀ J : Fin k → Fin n, pdT J (fun y ↦ f y - c) x = pdT J f x := fun J ↦ by
    rw [pdT, pdT, dT_sub hf contDiff_const]
    simp [dT, iteratedFDeriv_const_of_ne hk.ne']
  simp only [hsD, h]

theorem hsD_mul_sub_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ)
    (x : 𝔼) :
    hsD k (fun y ↦ f y * g y - f x * g y) x ≤
      ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  have hf' : ContDiff ℝ ∞ (fun y ↦ f y - f x) := hf.sub contDiff_const
  have e : (fun y ↦ f y * g y - f x * g y) = fun y ↦ (f y - f x) * g y := by
    funext y
    ring
  rw [e]
  refine (hsD_mul_le k hf' hg x).trans (le_of_eq ?_)
  rw [sum_filter]
  refine sum_congr rfl fun ij _ ↦ ?_
  split_ifs with h
  · rw [hsD_sub_const hf _ h]
  · have h0 : ij.1 = 0 := by omega
    rw [h0, hsD_zero]
    simp

theorem norm_mul_hsD_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ)
    (x : 𝔼) :
    ‖f x‖ * hsD k g x ≤ hsD k (fun y ↦ f y * g y) x +
      ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  have hfg : ContDiff ℝ ∞ (fun y ↦ f y * g y) := hf.mul hg
  have hr : ContDiff ℝ ∞ (fun y ↦ f y * g y - f x * g y) := hfg.sub (contDiff_const.mul hg)
  have e : (fun y ↦ f x * g y) = fun y ↦ f y * g y - (f y * g y - f x * g y) := by
    funext y
    ring
  rw [← hsD_const_mul hg, e]
  exact (hsD_sub_le hfg hr k x).trans (add_le_add le_rfl (hsD_mul_sub_le hf hg k x))

theorem hsD_mul_le' {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : 𝔼) :
    hsD k (fun y ↦ f y * g y) x ≤ ‖f x‖ * hsD k g x +
      ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  have hr : ContDiff ℝ ∞ (fun y ↦ f y * g y - f x * g y) :=
    (hf.mul hg).sub (contDiff_const.mul hg)
  have e : (fun y ↦ f y * g y) = fun y ↦ f x * g y + (f y * g y - f x * g y) := by
    funext y
    ring
  rw [e]
  refine (hsD_add_le (contDiff_const.mul hg) hr k x).trans ?_
  rw [hsD_const_mul hg]
  exact add_le_add le_rfl (hsD_mul_sub_le hf hg k x)

theorem norm_pderiv_mul_sub_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (α : Fin n → ℕ) (x : 𝔼) :
    ‖pderiv α (fun y ↦ f y * g y) x - f x * pderiv α g x‖ ≤
      ∑ ij ∈ (antidiagonal (mabs α)).filter (fun ij ↦ 0 < ij.1),
        ((mabs α).choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  have e : pderiv α (fun y ↦ f y * g y) x - f x * pderiv α g x =
      pderiv α (fun y ↦ f y * g y - f x * g y) x := by
    rw [pderiv_eq_dT', pderiv_eq_dT', pderiv_eq_dT', dT_sub (hf.mul hg) (contDiff_const.mul hg),
      dT_const_mul hg]
  rw [e]
  exact ((norm_pderiv_le _ α x).trans (norm_iteratedFDeriv_le_hsD _ _ x)).trans
    (hsD_mul_sub_le hf hg _ x)

theorem sqrt_sum_pdT_mul_sub_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (x : 𝔼) :
    Real.sqrt (∑ I : Fin k → Fin n, ‖pdT I (fun y ↦ f y * g y) x - f x * pdT I g x‖ ^ 2) ≤
      ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * hsD ij.1 f x * hsD ij.2 g x := by
  have e : ∀ I : Fin k → Fin n, pdT I (fun y ↦ f y * g y) x - f x * pdT I g x =
      pdT I (fun y ↦ f y * g y - f x * g y) x := fun I ↦ by
    rw [pdT, pdT, pdT, dT_sub (hf.mul hg) (contDiff_const.mul hg), dT_const_mul hg]
  simp_rw [e]
  exact hsD_mul_sub_le hf hg k x

theorem hsD_pderiv_le {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (α : Fin n → ℕ) (j : ℕ) (x : 𝔼) :
    hsD j (pderiv α f) x ≤ hsD (mabs α + j) f x := by
  refine (pow_le_pow_iff_left₀ (hsD_nonneg _ _ _) (hsD_nonneg _ _ _) two_ne_zero).1 ?_
  rw [hsD_sq, hsD_add_sq hf]
  refine sum_le_sum fun J _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [pdT_pderiv_comm hf]
  exact (norm_pderiv_le _ α x).trans (norm_iteratedFDeriv_le_hsD _ _ x)

end

end GroundTheory.Automorphic.Sobolev
