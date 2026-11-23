import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinear

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem tendsto_diffQuot_dw {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (f : E d → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin d)) (j : Fin d) {x : E d} (hx : x ∈ U) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (dw w f (x + (1 / ((n : ℝ) + 1)) • ev j) - dw w f x))
      atTop (𝓝 (dw (j :: w) f x)) := by
  have hn := hU.mem_nhds hx
  have hd : DifferentiableAt ℝ (dw w f) x :=
    ((contDiffOn_dw_of_isOpen hU w f hf).contDiffAt hn).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => dw w f (x + t • ev j)) (fderiv ℝ (dw w f) x (ev j)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • ev j) (ev j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ev j)).const_add x
    have h2 : HasFDerivAt (dw w f) (fderiv ℝ (dw w f) x) (x + (0:ℝ) • ev j) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have hs := hasDerivAt_iff_tendsto_slope.1 hline
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have h3 := hs.comp ht
  show Tendsto _ atTop (𝓝 (fderiv ℝ (dw w f) x (ev j)))
  refine h3.congr (fun n => ?_)
  simp only [Function.comp, slope_def_module, zero_smul, add_zero, sub_zero, Complex.real_smul]
  push_cast
  field_simp

theorem dw_continuousFunctional : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)),
    (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) →
    ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  intro d U hU B _ _ _ R hR hsm w
  induction w with
  | nil =>
    intro x hx
    exact ⟨⟨(LinearMap.proj x : (E d → ℂ) →ₗ[ℂ] ℂ).comp R, hR x hx⟩, fun u => rfl⟩
  | cons j w ih =>
    intro x hx
    choose! L hL using ih
    let y : ℕ → E d := fun n => x + (1 / ((n : ℝ) + 1)) • ev j
    let g : ℕ → B →L[ℂ] ℂ := fun n => ((n : ℂ) + 1) • (L (y n) - L x)
    have hev : ∀ᶠ n in atTop, y n ∈ U := by
      have hy : Tendsto y atTop (𝓝 x) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (ev j)
        simpa [y] using h0.const_add x
      exact hy (hU.mem_nhds hx)
    have hlim : Tendsto (fun n u => g n u) atTop (𝓝 (fun u => dw (j :: w) (R u) x)) := by
      rw [tendsto_pi_nhds]
      intro u
      refine (tendsto_diffQuot_dw hU (R u) (hsm u) w j hx).congr' ?_
      filter_upwards [hev] with n hn
      simp only [g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
        hL _ hn, hL _ hx, y]
    exact ⟨continuousLinearMapOfTendsto g hlim, fun u => rfl⟩

end GlobalTheory.HCA
